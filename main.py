import json
import math
import os

import javalang
import javalang.tree as Tree
import os, pickle
import re
import networkx as nx
import time
import sys
from memory_profiler import profile
import shutil
import gc


sys.setrecursionlimit(6000)
# for whw，此处需要修改为 '{本地路径}/spring-file/'
# split_path = 'E:/java_project/spring-file-oldbranch/'
split_path = 'F:/java_project/spring-file-oldbranch/'
# split_path = 'F:/java_parser/clicy-master/'
# split_path = 'C:/Users/wkr/Desktop/java_parser/clicy-master/'
no_class = []
assert split_path.endswith('/')

class TypeExceptin(Exception):
    "this is user's Exception for check the length of name "

    def __init__(self, str):
        self.str = str

    def __str__(self):
        print("该情况暂未处理:" + self.str)


class MethodNestingExceptin(Exception):
    "this is user's Exception for check the length of name "

    def __init__(self, str):
        self.str = str

    def __str__(self):
        print("方法嵌套:" + self.str)


def log(say, path='./log.txt'):
    print(say)
    with open(path, 'a') as file:
        file.write(say + '\n')


def get_pack_name(package_class_name):
    class_name = package_class_name.split('.')[-1]
    package_name = package_class_name.rstrip(class_name).rstrip('.')
    return class_name, package_name

def load_json(path):
    with open(path, 'rb') as f:
        data = json.load(f)
    return data


class AST_parse():
    def __init__(self):
        # 存储所有控制流语句节点 path索引 -> [node,father_api,children_api,False],false代表father是否和控制语句的第一个api链接
        self.control_node_dict = dict()
        # {参数名，[包名.类名,[参数列表]]}
        self.var_dict = dict()
        self.last_api = -1
        self.now_api = None
        self.neighbor_dict = dict()
        self.all_neighbor_dict = list()
        self.api_list = list()
        self.all_api_list = list()
        self.G = nx.Graph()
        self.all_desc_path = list()
        self.api_desc = str()
        # 存储所有项目内的api,其中不应包含继承到的api
        self.project_pack_dict = dict()
        # 存储项目内api的继承关系
        self.extend_dict = dict()
        # 记录所有无法正常解析的类
        self.parse_error_list = list()
        # 记录所有异常继承
        self.extend_error_list = {'parse_error': [], 'UNK_error': []}
        
        # self.pack_dict = self.load_pkl('api2desc.pkl')
        # 存储所有类所导入的包
        self.class_extend_methods = dict()
        # 记录每个包的路径
        self.pack_path_dict = dict()
        # 记录每个继承类的方法
        self.extend_class_methods = dict()
        # 记录所有接口信息
        self.project_pack_interface_dict = dict()
        # 记录所有实现关系
        self.implements_dict = dict()
        # 记录标准库结构dict
        self.jdk_structure_dict = self.load_json('ent_dict.json')

        self.parsed_method_nodes = set()

        def cook_ceir_hash(hash):
            hash = re.sub(r'<.*>', '', hash)
            hash = re.sub(r'PREVIEW', '', hash)
            return hash

        def create_pkl(ent_dict):
            pack_dict = {}
            for _, v in ent_dict.items():
                if v['type'] == 'package':
                    pack_dict[v['package']] = {}
                    for kw1 in ['contain class', 'contain interface', 'contain enum', 'contain record']:
                        for ceir_hash in v[kw1]: # 遍历类的哈希
                            ceir_hash = cook_ceir_hash(ceir_hash)
                            ceir_node = ent_dict[ceir_hash]
                            pack_dict[v['package']][ceir_node[ceir_node['type']]] = []
                            for kw2 in ['contain method', 'contain inherited method']:
                                for method_hash in ceir_node[kw2]:
                                    method_node = ent_dict[method_hash]
                                    method_name = method_node['method']
                                    method_param = []
                                    for param_hash, _ in method_node['parameter']:
                                        param_node = ent_dict[param_hash]
                                        param_package = param_node['package'] if 'package' in param_node else ''
                                        param_name = param_node[param_node['type']]
                                        if len(param_package) > 0:
                                            method_param.append(param_package + '.' + param_name)
                                        else:
                                            assert param_name in ('byte', 'float', 'double', 'int', 'short', 'long', 'boolean', 'char', 'void', 'generics')
                                            method_param.append(param_name)
                                    method_return_hash_and_dim = method_node['return']
                                    method_return = None
                                    if method_return_hash_and_dim != 'None':
                                        method_return_hash = method_return_hash_and_dim[0]
                                        method_return_node = ent_dict[method_return_hash]
                                        return_package = method_return_node['package'] if 'package' in method_return_node else ''
                                        if len(return_package) > 0:
                                            method_return = method_return_node['package'] + '.' + method_return_node[method_return_node['type']]
                                        else:
                                            assert method_return_node[method_return_node['type']] in ('byte', 'float', 'double', 'int', 'short', 'long', 'boolean', 'char', 'void', 'generics')
                                            method_return = method_return_node[method_return_node['type']]
                                    method_field = method_node['field']
                                    pack_dict[v['package']][ceir_node[ceir_node['type']]].append([method_name, method_param, method_return, method_field])
            return pack_dict
        # 存储所有标准库api信息
        self.pack_dict = create_pkl(self.jdk_structure_dict)
        self.static_method_dict = dict()
        for key, value in self.pack_dict.get('java.lang').items():
            static_methods = [method for method in value if 'static' in method[-1]]
            if static_methods:
                self.static_method_dict[key] = static_methods
        # # spring文档中爬取到的api信息
        # self.doc_project_dict = self.load_json(f'./doc_project_dict/{subdir}')
        # 存储所有包含外部类的class。格式 包名.主类名 -》 [外部类]
        self.out_class_dict = dict()
        # 存储项目中每一个类所导入加自身的方法之和
        self.project_import_dict = dict()
        # 存储classhash
        self.project_class_hash = dict()
        # 存储类的field
        self.project_class_field = dict()
        # 存储方法hash
        self.project_method_hash = dict()
        # 存项目结构
        self.project_structure_dict = dict()
        # 存储变量维度
        self.project_var_dimensions = dict()
        # 存所有全局变量
        self.field_var_dict = dict()

        for temp_hash in self.jdk_structure_dict.keys():
            temp_decs = temp_hash.split('$')
            if temp_decs[0] in ('class', 'interface', 'enum', 'record'):
                temp_pack_name = temp_decs[-2]
                temp_class_name = temp_decs[-1]
                # if f'{temp_pack_name}.{temp_class_name}' == 'java.lang.Character.UnicodeScript':
                #     pass
                self.project_class_hash[f'{temp_pack_name}.{temp_class_name}'] = temp_hash
            elif temp_decs[0] == 'package':
                temp_pack_name = temp_decs[-1]
                self.project_class_hash[temp_pack_name] = temp_hash
            elif temp_decs[0] == 'method':
                temp_pack_name = temp_decs[-3]
                temp_class_name = temp_decs[-2]
                temp_method_name = re.split('\(|\)', temp_decs[-1])
                method_key = temp_method_name[0] + '+' + temp_method_name[1]
                if not self.project_method_hash.__contains__(f'{temp_pack_name}.{temp_class_name}'):
                    self.project_method_hash[f'{temp_pack_name}.{temp_class_name}'] = {method_key: temp_hash}
                else:
                    self.project_method_hash.get(f'{temp_pack_name}.{temp_class_name}')[method_key] = temp_hash

    def clear_self(self):
        self.control_node_dict = dict()
        # {参数名，[包名.类名,[参数列表]]}
        self.var_dict = dict()
        self.last_api = -1
        self.now_api = None
        self.neighbor_dict = dict()
        self.all_neighbor_dict = list()
        # self.api_list = list()
        self.all_api_list = list()
        self.api_desc = str()

    def get_method_field(self, field_list, modifiers):
        m_type = set(field_list).intersection(set(modifiers))
        return m_type

    # 获得类及内部类中的方法
    def processing_project_api_nodes(self, tree, class_name, maindir, pakage_name='', flag=False):
        # if class_name == 'RabbitListenerAnnotationBeanPostProcessor':
        #     print('a')
        out_class = []
        inner_class = []
        pack_path = maindir.removeprefix(split_path)
        package_project = pack_path.split('/')[0]
        if class_name == 'package-info':
            return 0
        for path, node in tree:
            if not flag and not isinstance(node, Tree.CompilationUnit):
                try:
                    inner_class = [inner_node for inner_node in node.body if
                                   isinstance(inner_node, Tree.ClassDeclaration)]
                except IndexError:
                    print(f'文件{maindir}/{class_name}.java获取包内api时出现问题')
                    break
                flag = True

            # 提取导入类，并获得包信息
            if isinstance(node, Tree.CompilationUnit):
                try:
                    out_class = [out_node for out_node in node.children[-1] if not out_node.name == class_name]
                    if out_class:
                        self.out_class_dict[f'{pakage_name}.{class_name}'] = list()
                        for out_class_node in out_class:
                            self.out_class_dict[f'{pakage_name}.{class_name}'].append(out_class_node.name)
                    inner_class = [inner_node for inner_node in node.children[-1][0].body if
                                   isinstance(inner_node, Tree.ClassDeclaration)]

                except IndexError:
                    print(f'文件{maindir}/{class_name}.java获取包内api时出现问题')
                    break
                flag = True
                # if inner_class:
                #     break
                if node.package:
                    pakage_name = node.package.name
                    # if pakage_name == 'org.springframework.amqp.rabbit.annotation':
                    #     print('a')
                    if not self.project_pack_dict.__contains__(pakage_name):
                        self.project_pack_dict[pakage_name] = dict()

                        self.project_class_hash[pakage_name] = f'package${package_project}${pakage_name}'
                        self.pack_path_dict[pakage_name] = maindir
                    # 防止同包名
                    elif self.pack_path_dict[pakage_name] != maindir:
                        self.pack_path_dict[f'{pakage_name}_2'] = maindir
                    self.project_pack_dict[pakage_name][class_name] = list()
                else:
                    break

            # elif isinstance(node, Tree.ConstructorDeclaration) and not (
            #         isinstance(tree, Tree.CompilationUnit) and (path[-2] in inner_class
            #                                                     or path[-2] in out_class)):
            elif isinstance(node, Tree.ConstructorDeclaration) and not (path[-2] in inner_class or path[-2] in out_class):
                params = list()
                for p in node.parameters:
                    params.append(p.type.name)
                if not self.project_pack_dict[pakage_name].__contains__(class_name):
                    self.project_pack_dict[pakage_name][class_name] = list()
                self.project_pack_dict[pakage_name][class_name].append([node.name, f'{maindir}/{class_name}', params,
                                                                        None, ['public']]) # TODO
            elif isinstance(node, Tree.EnumDeclaration):
                break
            elif isinstance(node, Tree.ClassDeclaration) or isinstance(node, Tree.InterfaceDeclaration):
                # 如果包含内部类的话
                # TODO:内部类中的方法内部类还未解决
                class_interface = 'class' if isinstance(node, Tree.ClassDeclaration) else 'interface'
                self.project_class_hash[
                    f'{pakage_name}.{class_name}'] = f'{class_interface}${package_project}${pakage_name}${class_name}'
                self.project_class_field[f'{pakage_name}.{class_name}'] = node.modifiers if node.modifiers else ['protected']
                if node in inner_class:
                    # if node.name == 'HeadersExchangeMapConfigurer':
                    #     print('a')
                    self.processing_project_api_nodes(node, f'{class_name}.{node.name}', maindir, pakage_name, False)
                elif node in out_class:
                    self.processing_project_api_nodes(node, node.name, maindir, pakage_name, False)
                else:
                    if isinstance(node, Tree.ClassDeclaration):
                        # 如果没有构造器加入一个构造器方法
                        constructors = [constructor for constructor in node.body if
                                        isinstance(constructor, Tree.ConstructorDeclaration)]
                        if not constructors:
                            if not self.project_pack_dict[pakage_name].__contains__(class_name):
                                self.project_pack_dict[pakage_name][class_name] = list()
                            # TODO:路径该怎么写
                            self.project_pack_dict[pakage_name][class_name].append(
                                [node.name, f'{maindir}/{class_name}', [], None, ['public']])
                    else:
                        if not self.project_pack_interface_dict.__contains__(pakage_name):
                            self.project_pack_interface_dict[pakage_name] = dict()
                        if not self.project_pack_interface_dict[pakage_name].__contains__(class_name):
                            self.project_pack_interface_dict[pakage_name][class_name] = self.project_pack_dict.get(
                                pakage_name).get(class_name)
            elif isinstance(node, Tree.MethodDeclaration) and not (path[-2] in inner_class or path[-2] in out_class):
                if not isinstance(path[-2], Tree.ClassDeclaration) or isinstance(path[-2], Tree.InterfaceDeclaration):
                    continue
                # if node.name == 'toMessage':
                #     print('a')
                if isinstance(path[-2], Tree.InterfaceDeclaration):
                    m_type = ['public']
                else:
                    m_type = list(node.modifiers)
                    modifier_types = {'public', 'protected', 'private', 'default'}
                    if not modifier_types.intersection(node.modifiers):
                        m_type.append('default')
                    if not m_type:
                        m_type = ['default']
                params = list()
                params_dimensions = list()
                for p in node.parameters:
                    params.append(p.type.name)
                    params_dimensions.append([p.type.name, len(p.type.dimensions)])
                if not self.project_pack_dict[pakage_name].__contains__(class_name):
                    self.project_pack_dict[pakage_name][class_name] = list()
                assert type(m_type) is list
                self.project_pack_dict[pakage_name][class_name].append([node.name, f'{maindir}/{class_name}', params,
                                                                        node.return_type.name if node.return_type else None,
                                                                        m_type])

    def get_project_api(self, dirname):
        for maindir, subdir, file_name_list in os.walk(dirname):
            maindir = maindir.replace('\\', '/')
            for java_file in file_name_list:
                if java_file.endswith('.java'):
                    apath = os.path.join(maindir, java_file)
                    # print(apath)

                    class_name = java_file.rstrip('java').rstrip('.')
                    try:
                        f_input = open(apath, 'r', encoding='utf-8')
                        f_read = f_input.read()
                    except:
                        print(f'文件{maindir}/{java_file}获得初步api时读取失败 ')
                        continue
                    try:
                        tree = javalang.parse.parse(f_read)
                    except:
                        print(f'文件{maindir}/{java_file}获得初步api时无法解析 ')
                        self.parse_error_list.append(java_file.removesuffix('.java'))
                        error_maindir = maindir.removeprefix(split_path)
                        write_file('./error/errorfile.txt', f'{error_maindir}/{java_file}\n')
                        continue

                    self.processing_project_api_nodes(tree, class_name, maindir)

    # 获得参数和返回值的所在包
    # TODO:把导入包的内容存起来，容易溢出
    # @profile
    def get_re_param(self, dirname):
        for maindir, subdir, file_name_list in os.walk(dirname):
            maindir = maindir.replace('\\', '/')
            pack_path = maindir.removeprefix(split_path)
            package_project = pack_path.split('/')[0]
            for java_file in file_name_list:
                if java_file.endswith('.java'):
                    apath = f'{maindir}/{java_file}'
                    # print(apath)
                    class_name = java_file.rstrip('java').rstrip('.')
                    # if class_name == 'ClientHttpRequestFactoryFactory':
                    #     print('a')
                    try:
                        f_input = open(apath, 'r', encoding='utf-8')
                        f_read = f_input.read()
                    except:
                        print(f'文件{maindir}/{java_file}获取返回值参数时读取文件失败')
                    try:
                        tree = javalang.parse.parse(f_read)
                    except:
                        print(f'文件{maindir}/{java_file}获取返回值参数时解析文件失败')
                        # self.parse_error_list.append(java_file.removesuffix('.java'))
                        # error_maindir = maindir.removeprefix(split_path)
                        # write_file('./error/errorfile.txt', f'{error_maindir}/{java_file}\n')
                        continue
                    # TODO:extend
                    import_dict = [dict(), dict(), dict()]
                    class_meths_dict = [dict(), dict(), dict()]
                    for key, value in self.pack_dict.get('java.lang').items():
                        class_meths_dict[2][key] = [method for method in value if 'public' in method[-1]]
                    for temp_class_name in class_meths_dict[2].keys():
                        import_dict[2][temp_class_name] = 'java.lang'
                    for path, node in tree:
                        if isinstance(node, Tree.CompilationUnit):
                            # TODO:内部类暂时删掉
                            try:
                                out_class = [out_node for out_node in node.children[-1] if
                                             not out_node.name == class_name]
                                inner_class = [inner_node for inner_node in node.children[-1][0].body if
                                               isinstance(inner_node, Tree.ClassDeclaration)]
                                # 解决在类中调用本类中内部类的问题
                                class_name_dict = {class_name:class_name}
                                for temp_class_name in [temp_node.name for temp_node in inner_class + out_class]:
                                    class_name_dict[temp_class_name] = f'{class_name}.{temp_class_name}'
                            except Exception as e:
                                # print(e)
                                break
                            # 提取导入类，并获得包信息
                            if node.package:
                                package_name = node.package.name
                                # if package_name == 'org.springframework.amqp.core':
                                #     print('a')
                                pakage_inside_class = self.project_pack_dict.get(node.package.name)
                                for key, value in pakage_inside_class.items():
                                    class_meths_dict[0][key] = [method for method in value if
                                                                not self.get_method_field(['private', 'father_project'],
                                                                                          method[-1])]
                                for temp_class_name in pakage_inside_class.keys():
                                    import_dict[0][temp_class_name] = node.package.name
                            else:
                                break
                            # Import完成后，去除同名方法
                            if node.imports:
                                for import_node in node.imports:
                                    class_meths_dict, import_dict = self.parse_import_node(class_meths_dict,
                                                                                           import_dict, import_node)
                            class_meths_dict[2].update(class_meths_dict[1])
                            class_meths_dict[2].update(class_meths_dict[0])
                            class_meths_dict = class_meths_dict[2]
                            import_dict[2].update(import_dict[1])
                            import_dict[2].update(import_dict[0])
                            import_dict = import_dict[2]
                            if not self.project_import_dict.__contains__(package_name):
                                self.project_import_dict[package_name] = dict()
                            self.project_import_dict[package_name][class_name] = [class_meths_dict, import_dict]
                            # self.project_import_dict[package_name][class_name] = []
                        elif isinstance(node, Tree.EnumDeclaration):
                            break

                        elif isinstance(node, Tree.ClassDeclaration) or isinstance(node, Tree.InterfaceDeclaration):
                            other_class = None
                            other_class_name = class_name
                            if node in inner_class:
                                other_class = node
                                other_class_name = f'{class_name}.{node.name}'
                                self.project_import_dict[package_name][other_class_name] = [class_meths_dict,
                                                                                            import_dict]
                            elif node in out_class:
                                other_class = node
                                other_class_name = node.name
                                self.project_import_dict[package_name][other_class_name] = [class_meths_dict,
                                                                                            import_dict]
                            # 如果内部类中出现内部类
                            elif node.name != class_name and (isinstance(path[-2], Tree.ClassDeclaration) or isinstance(path[-2], Tree.InterfaceDeclaration)):
                                if path[-2].name in class_name_dict.keys():
                                    father_name = class_name_dict.get(path[-2].name)
                                    class_name_dict[node.name] = f'{father_name}.{node.name}'
                            # 暂时
                            elif node.name != class_name:
                            #     TODO
                            #     print('出现方法内部类')
                                no_class.append(f'{apath}-{node.name}')
                                continue
                            # if other_class_name == 'OMPP':
                            #     print('a')
                            constructors = [constructor for constructor in node.body if
                                            isinstance(constructor, Tree.ConstructorDeclaration)]
                            if not constructors and isinstance(node, Tree.ClassDeclaration):
                                if not self.project_var_dimensions.__contains__(f'{package_name}.{other_class_name}'):
                                    # print('a')
                                    self.project_var_dimensions[f'{package_name}.{other_class_name}'] = [[[], [None, 0]]]
                            if node.extends:
                                if isinstance(node, Tree.ClassDeclaration):
                                    extend_name = node.extends.name
                                    father_package_name = import_dict.get(extend_name)
                                    if not father_package_name and extend_name in class_name_dict.keys():
                                        father_package_name = package_name
                                        if not extend_name == class_name:
                                            extend_name = class_name_dict.get(extend_name)
                                    elif (not father_package_name) and (extend_name in self.parse_error_list):
                                        self.extend_error_list['parse_error'].append([f'{pack_path}/{class_name}.java', extend_name])
                                    elif not father_package_name:
                                        self.extend_error_list['UNK_error'].append([f'{pack_path}/{class_name}.java', extend_name])
                                    self.extend_dict[
                                        f'{package_name}.{other_class_name}'] = f'{father_package_name}.{extend_name}'
                                else:
                                    extend_list = list()
                                    for temp_extend_node in node.extends:
                                        temp_extend_name = temp_extend_node.name
                                        extend_list.append(f'{import_dict.get(temp_extend_name)}.{temp_extend_name}')
                                    self.extend_dict[f'{package_name}.{other_class_name}'] = extend_list
                            if isinstance(node, Tree.ClassDeclaration) and node.implements:
                                self.implements_dict[f'{package_name}.{other_class_name}'] = list()
                                for implement_class_type in node.implements:
                                    self.implements_dict[
                                        f'{package_name}.{other_class_name}'].append(
                                        f'{import_dict.get(implement_class_type.name)}.{implement_class_type.name}')

                        elif isinstance(node, Tree.FieldDeclaration):
                            if other_class and node in other_class.body:
                                temp_class_name = other_class_name
                            else:
                                temp_class_name = class_name
                            if not self.field_var_dict.__contains__(package_name):
                                self.field_var_dict[package_name] = dict()
                            if not self.field_var_dict.get(package_name).__contains__(temp_class_name):
                                self.field_var_dict.get(package_name)[temp_class_name] = list()
                            if not isinstance(node.type, Tree.BasicType):
                                # TODO:如果是内部类的话可能找不到，内部类的导入调用也成问题
                                var_hash = self.project_class_hash.get(
                                    f'{import_dict.get(node.type.name)}.{node.type.name}')
                            else:
                                var_hash = f'basictype${node.type.name}'
                            var_type = [var_hash, len(node.type.dimensions)]
                            var_field = list(node.modifiers)
                            var_member = node.declarators[0].name
                            self.field_var_dict[package_name][temp_class_name].append(
                                [f'member${package_project}${package_name}$'
                                 f'{temp_class_name}', var_type, var_field, var_member])

                        # 构造函数需要处理
                        elif isinstance(node, Tree.MethodDeclaration) or isinstance(node, Tree.ConstructorDeclaration):
                            # if node.name == 'toMessage':
                            #     print('a')
                            if other_class and node in other_class.body:
                                temp_class_name = other_class_name
                            else:
                                temp_class_name = class_name
                            params = list()
                            params_dimensions = list()
                            for p in node.parameters:
                                params.append(p.type.name)
                            if isinstance(node, Tree.ConstructorDeclaration):
                                return_type = None
                            else:
                                return_type = node.return_type.name if node.return_type else None
                            all_method_list = self.project_pack_dict.get(package_name).get(temp_class_name)
                            if not self.project_var_dimensions.__contains__(f'{package_name}.{temp_class_name}'):
                                self.project_var_dimensions[f'{package_name}.{temp_class_name}'] = list()
                            if all_method_list:
                                for i in range(len(all_method_list)):
                                    if all_method_list[i][0] == node.name and all_method_list[i][-3] == params and \
                                            all_method_list[i][-2] == return_type:
                                        params.clear()
                                        for p in node.parameters:
                                            if not p.type.name in basic_type:
                                                p.type.name = f'{import_dict.get(p.type.name)}.{p.type.name}'
                                            params.append(p.type.name)
                                            params_dimensions.append([p.type.name, len(p.type.dimensions)])
                                        if return_type:
                                            if return_type in class_name_dict.keys():
                                                return_type = class_name_dict.get(return_type)
                                            if not return_type in basic_type:
                                                return_type = f'{import_dict.get(return_type)}.{return_type}'
                                            return_type_dimensions = [return_type, len(node.return_type.dimensions)]
                                            self.project_pack_dict.get(package_name).get(temp_class_name)[i][
                                                3] = return_type
                                        elif isinstance(node, Tree.ConstructorDeclaration):
                                            return_type_dimensions = [None, 0] # 'None'
                                        else:
                                            return_type_dimensions = ['void', 0]
                                        self.project_pack_dict.get(package_name).get(temp_class_name)[i][
                                            2] = params
                                        self.project_var_dimensions.get(f'{package_name}.{temp_class_name}').append(
                                            [params_dimensions, return_type_dimensions])
                                        break
        # gc.collect()

    # TODO:会出现包名重复的问题
    def get_extend_pakage(self, package_class_name):

        def add_father_methods(class_meths_dict, extend_package_class_name):
            extend_class_name, extend_package_name = get_pack_name(extend_package_class_name)
            father_methods_list = list(self.get_extend_pakage(extend_package_class_name))
            for method in father_methods_list:
                if 'final' in method[-1] or 'static' in method[-1]:
                    continue
                if method[0] == extend_class_name:
                    continue
                if 'protected' in method[-1]:
                    method[-1].replace('protected', 'father_protected')
                    class_methods_list.append(method)
                    try:
                        class_meths_dict[class_name].append(method)
                    except:
                        class_meths_dict[class_name] = [method]
                elif self.get_method_field(['public', 'father_protected'], method[-1]):
                    class_methods_list.append(method)
                    try:
                        class_meths_dict[class_name].append(method)
                    except:
                        class_meths_dict[class_name] = [method]

        if package_class_name == '':
            return []
        class_name, package_name = get_pack_name(package_class_name)
        class_methods_list = list()
        if self.extend_class_methods.__contains__(package_class_name):
            return self.extend_class_methods.get(package_class_name)
        # 如果继承的是标注库类
        elif self.pack_dict.__contains__(package_name):
            father_methods_list = list(self.pack_dict.get(package_name).get(class_name))
            for method in father_methods_list:
                if 'final' in method[-1] or 'static' in method[-1]:
                    continue
                if 'protected' in method[-1]:
                    method[-1].replace('protected', 'father_protected')
                    class_methods_list.append(method)
                # TODO:father_protected
                elif self.get_method_field(['public', 'father_protected'], method[-1]):
                    class_methods_list.append(method)
            return class_methods_list
        # 如果继承的是包内类

        # 为解决项目下有两个同名包
        try:
            class_methods_list.extend(self.project_pack_dict.get(package_name).get(class_name))
        except:
            return []
        if not self.extend_dict.__contains__(package_class_name):
            return class_methods_list
        class_meths_dict = self.project_import_dict.get(package_name).get(class_name)[0]

        # 增添新属性：'father_protected'，子类可继承但跨包不可调用
        # 这条判断语句其实没用了，但是不删了吧
        extend_package_class_name = self.extend_dict.get(package_class_name)
        if not extend_package_class_name:
            return class_methods_list
        if isinstance(extend_package_class_name, list):
            for temp_extend_package_class_name in extend_package_class_name:
                add_father_methods(class_meths_dict, temp_extend_package_class_name)
        else:
            add_father_methods(class_meths_dict, extend_package_class_name)
        self.extend_class_methods[package_class_name] = class_methods_list
        return class_methods_list

    def get_extend_methods(self):
        # for package_class_name, apath in self.extend_dict.items():
        for package_class_name in list(self.extend_dict.keys()):
            try:
                self.extend_class_methods[package_class_name] = self.get_extend_pakage(package_class_name)
            except:
                pass

    def parse_import_node(self, class_meths_dict, import_dict, node):

        def full_path_import(temp_dict, pack_name, class_name):
            temp_class_methods = temp_dict.get(pack_name).get(class_name)
            # if not temp_class_methods:
            #     print('a')
            if isinstance(temp_class_methods, list):
                class_meths_dict[1][class_name] = [method_decs for method_decs in temp_class_methods if
                                                   'public' in method_decs[-1]]
                import_dict[1][class_name] = pack_name

        def unfull_path_import(this_dict):
            pack_contain_class = this_dict.get(node.path)
            if not pack_contain_class:
                print('a')
            # class_meths_dict[2].update(pack_contain_class)
            for key, value in pack_contain_class.items():
                class_meths_dict[2][key] = [method_decs for method_decs in value if 'public' in method_decs[-1]]
            for class_name in pack_contain_class.keys():
                import_dict[2][class_name] = node.path

        def out_class_import(this_dict):
            if self.out_class_dict.__contains__(node.path):
                out_class_names = self.out_class_dict.get(node.path)
                for out_class_name in out_class_names:
                    full_path_import(this_dict, pack_name, out_class_name)

        # undo .*情况node.path没有*
        # class_pack_dict   类名 -》 [包和[所有方法[方法名，参数（可能为none），返回值（可能为void）]]]
        # 需要判断该引用是否是标准库
        if self.project_pack_dict.__contains__(node.path):
            unfull_path_import(self.project_pack_dict)

        elif self.pack_dict.__contains__(node.path):  #./引用
            unfull_path_import(self.pack_dict)
        elif all_doc_project_dict.__contains__(node.path):  # ./引用
            unfull_path_import(all_doc_project_dict)
        else:
            class_name = node.path.split('.')[-1]
            pack_name = node.path.rstrip(class_name).rstrip('.')
            if self.pack_dict.__contains__(pack_name):
                full_path_import(self.pack_dict, pack_name, class_name)
            elif self.project_pack_dict.__contains__(pack_name):
                full_path_import(self.project_pack_dict, pack_name, class_name)
                out_class_import(self.project_pack_dict)
            elif all_doc_project_dict.__contains__(pack_name):
                full_path_import(all_doc_project_dict, pack_name, class_name)
                out_class_import(all_doc_project_dict)

        return class_meths_dict, import_dict



    def load_pkl(self, path):
        with open(path, 'rb') as f:
            data = pickle.load(f)
        return data

    def load_json(self, path):
        with open(path, 'rb') as f:
            data = json.load(f)
        return data

    def while_load_pkl(self, path):
        num = 0
        with open(path, 'rb') as f:
            while True:
                try:
                    aa = pickle.load(f)
                    # print(aa.__sizeof__())
                    num += len(aa)
                    # self.dump_pkl_notCover('desc_path_dict.pkl', aa)
                    # if(len(aa) == 141):
                    #     break
                    #     print('写入成功')
                except EOFError:
                    break
        print(num)

    def dump_pkl_cover(self, path, path_list):
        with open(path, 'wb') as f:
            pickle.dump(path_list, f)

    def dump_pkl_notCover(self, path, path_list):
        with open(path, 'ab') as f:
            pickle.dump(path_list, f)

    # undo 查询字面常量Literal是int,float,double,String,char[]中的哪一种
    def judge_Literal(self, node):
        literal = node.value
        type_name = None
        if literal[0] == '\'' and literal[-1:] == '\'':
            type_name = 'char[]'
        elif literal[0] == '\"' and literal[-1:] == '\"':
            type_name = 'java.lang.String'
        elif literal == 'true' or literal == 'false':
            type_name = 'boolean'
        elif re.compile(r'^[-+]?[0-9]+$').match(literal):
            type_name = 'int'
        elif re.compile(r'^[-+]?[0-9]+\.[0-9]+$').match(literal):
            type_name = 'float'
        return type_name

    def get_api_decs_lists(self, last_method_node, import_dict, package_name, class_name):
        self.all_api_list.append(list(self.api_list))
        params = list()
        for p in last_method_node.parameters:
            params.append(p.type.name)
            # params.append(f'{import_dict.get(p.type.name)}.{p.type.name}')
        path_method_hash = self.project_method_hash.get(f'{package_name}.{class_name}').get(
            last_method_node.name + '+' + ','.join(params))
        if not self.api_desc == '' and path_method_hash and not None in self.api_list:
            self.all_desc_path.append({
                'description': self.api_desc,
                'method': path_method_hash,
                'api sequences': self.api_list.copy()
            })
        self.api_desc = ''
        self.G.clear()
        self.var_dict.clear()
        self.api_list.clear()
        self.all_neighbor_dict.append(dict(self.neighbor_dict))
        self.neighbor_dict.clear()
        self.control_node_dict.clear()
        self.last_api = -1

    def parse_java_file(self, java_file, maindir):
        # 为了释放内存可以考虑存储hash值 或者考虑用set 或者用队列弹出


        # 根据给定的重载方法找到匹配的
        def get_overload_method_2(temp_node, overload_method):
            if not overload_method:
                return None
            try:
                argu_type_list = list()
                if not temp_node.arguments:
                    raise MethodNestingExceptin("没有参数")
                for argument in temp_node.arguments:
                    if isinstance(argument, Tree.MemberReference):
                        try:
                            argu_type_list.append(self.var_dict.get(argument.member)[0])
                        except TypeError:
                            argu_type_list.append(argument.member)
                    elif isinstance(argument, Tree.Literal):
                        argu_type_list.append(self.judge_Literal(argument))
                    elif isinstance(argument, Tree.BinaryOperation):
                        argu_type_list.append('int')
                    elif isinstance(argument, Tree.MethodInvocation):
                        parse_methodInvocation(argument)
                    else:
                        raise MethodNestingExceptin("如果参数中包含方法调用，则随即返回一个参数数量相等的方法")
                if len(overload_method) > 0 and len(overload_method[0]) == 2:
                    right_method = overload_method[0]
                elif len(overload_method) > 1:
                    right_method = None
                    for method in overload_method:
                        if method[1] == argu_type_list:
                            right_method = method
                    if not right_method:
                        raise MethodNestingExceptin("没有找到匹配的重载函数,随即返回")

                elif len(overload_method) == 1:
                    right_method = overload_method[0]
                else:
                    right_method = None
                # 返回类型：[方法名，[参数]，返回值]
                return right_method
            except MethodNestingExceptin:
                argu_num = len(temp_node.arguments)
                # right_method = [method for method in overload_method if (len(method[1].split(',')) == argu_num)][0]
                for method in overload_method:
                    if method[1] and len(method[1]) == argu_num:
                        right_method = method
                        break
                    elif (not method[1]) and argu_num == 0:
                        right_method = method
                        break
                    else:
                        right_method = None
                if not right_method:
                    right_method = overload_method[0]
                return right_method

        # 通过函数调用节点的方法名及参数，查询出符合的库函数
        def get_overload_method(temp_node):
            try:
                var_name = temp_node.qualifier
                if '.' in var_name:
                    temp_node.qualifier = var_name.split('.')[-1]
                    method_list = class_meths_dict.get(var_name.split('.')[-1])
                else:
                    method_list = self.var_dict[var_name][1]
                overload_method = [method for method in method_list if method[0] == temp_node.member]
                if not overload_method:
                    return None
                # undo 当重叠调用时，参数包含MethodInvocation，和MemberReference两种
                # 当时内部函数时，暂时添加参数返回值，无法确认重载方法
                return get_overload_method_2(temp_node, overload_method)
            except TypeExceptin as e:
                print(e.str)

            except BaseException:
                pass

        def get_father_return_class():
            path_len = len(path) - 1
            if isinstance(path[path_len], list):
                path_len -= 1
            father_node = path[path_len]
            father_return_class = None
            # undo 如果是两层掉用，则拿到第二层的变量
            # 如果不包含在self.var_dict中，说明不是标准库函数
            if hasattr(father_node, 'qualifier') and (self.var_dict.__contains__(father_node.qualifier)):
                method_decs = get_overload_method(father_node)
                if method_decs:
                    # TODO:返回值
                    father_return_class = method_decs[-2]
            # 返回格式 包+类名
            return father_return_class

        def append_method_hash(method_key, temp_pack_class_name, temp_node, temp_method_decs):

            if self.project_method_hash.__contains__(temp_pack_class_name):
                self.parsed_method_nodes.add(temp_node)
                path_method_hash = self.project_method_hash.get(temp_pack_class_name).get(method_key)
                if not path_method_hash and isinstance(node, Tree.MethodInvocation):
                    temp_overload_methods = [temp_method for temp_key, temp_method in self.project_method_hash.get(temp_pack_class_name).items()
                                             if temp_key.split('+')[0] == temp_node.qualifier]
                    if temp_overload_methods:
                        path_method_hash = temp_overload_methods[0]
                    else:
                        return False
                self.api_list.append(path_method_hash)
                return True
            elif project_class_hash.__contains__(temp_pack_class_name):
                class_clash = project_class_hash.get(temp_pack_class_name)
                project_name = class_clash.split('$')[1]
                other_project_class = load_json(f'./structure_file_fromhw/{project_name}.structure.json')[class_clash]
                contain_method = other_project_class['contain method'] + other_project_class['contain inherited method']
                for temp_method in contain_method:
                    method_name = temp_method.split('$')[-1].split('(')[0]
                    if not method_name == temp_method_decs[0]:
                        continue
                    param = temp_method.split('$')[-1].removeprefix(f'{method_name}(').removesuffix(')')
                    if not param:
                        param_num = 0
                    else:
                        param_num = len(param.split(','))
                    if param_num == len(temp_method_decs[-3]):
                        self.api_list.append(temp_method)
                        self.parsed_method_nodes.add(temp_node)
                        return True
                        break
            else:
                return False

        def parse_methodInvocation(temp_node):
            # if temp_node.member== 'registerDeliveryTag':
            #     print('a')
            if temp_node in self.parsed_method_nodes:
                return False
            if self.var_dict.__contains__(temp_node.qualifier):
                var_name = temp_node.qualifier
                method_decs = get_overload_method(temp_node)
                if method_decs:
                    param_list = [temp_method.split('.')[-1] for temp_method in method_decs[-3]]
                    method_key = method_decs[0] + '+' + ','.join(param_list)
                    append_method_hash(method_key, self.var_dict[var_name][0], temp_node, method_decs)
                    return method_decs[2]
            # 当连续调用
            elif not temp_node.qualifier:
                # 如果是调用本类方法
                if not lines[temp_node.position.line - 1][temp_node.position.column - 2] == '.':
                # if isinstance(path[-1], Tree.StatementExpression) or temp_node.member in [method[0] for method in this_class_methods]:
                    try:
                        method_decs = [method for method in this_class_methods if method[0] == temp_node.member][0]
                        if method_decs:
                            param_list = [temp_method.split('.')[-1] for temp_method in method_decs[-3]]
                            method_key = method_decs[0] + '+' + ','.join(param_list)
                            append_method_hash(method_key, f'{package_name}.{class_name}', temp_node, method_decs)
                            return method_decs[2]
                    except:
                        return False
                var_father_return_class = get_father_return_class()
                # TODO:返回
                if var_father_return_class:
                    if 'None' in var_father_return_class:
                        self.api_list.append(f'E.{temp_node.member}(UNKNOW)')
                        self.parsed_method_nodes.add(temp_node)
                        return False
                    # 当父节点返回为正常类
                    else:
                        temp_node.qualifier = var_father_return_class
                        method_decs = get_overload_method(temp_node)
                        if method_decs:
                            param_list = [temp_method.split('.')[-1] for temp_method in method_decs[-3]]
                            method_key = method_decs[0] + '+' + ','.join(param_list)
                            try:
                                append_method_hash(method_key, var_father_return_class, temp_node, method_decs)
                                return method_decs[-2]
                            except:
                                return False

        java_type = ['byte[]', 'char', 'short', 'int', 'long', 'float', 'double', 'boolean']
        # TODO:没有解决内部类的问题，例：'E:/java_project/github_file_4/3d-bin-container-packing-master\\core\\src\\main\\java\\com\\github\\skjolber\\packing\\iterator\\DefaultPermutationRotationIterator.java'
        error_list = ['DefaultPermutationRotationIterator.java', 'TranscodeScheme.java', 'TransactionalLock.java',
                      'package-info.java']
        if java_file in error_list:
            return False
        class_name = java_file.split('.')[0]
        self.clear_self()
        apath = f'{maindir}/{java_file}'
        try:
            f_input = open(apath, 'r', encoding='utf-8')
            f_read = f_input.read()
        except:
            print(f'文件{maindir}/{java_file}获得api序列时无法读取文件')
            return False
        try:
            tree = javalang.parse.parse(f_read)
        except:
            print(f'文件{maindir}/{java_file}获得api序列时解析失败')
            return False
        f_input.seek(0)
        lines = f_input.readlines()
        last_node_position = 0
        last_method_node = None
        # print(apath)
        # if class_name == 'RabbitTemplate':
        #     print('1')
        self.api_list.clear()
        self.parsed_method_nodes.clear()
        # print(apath)
        # if apath == 'E:/java_project/github_file/aeron-master/aeron-test-support/src/main/java/io/aeron/test/DataCollector.java':
        #     print('a')
        for path, node in tree:
            # print(node)
            if isinstance(node, Tree.CompilationUnit):
                # TODO:内部类暂时删掉

                # 提取导入类，并获得包信息
                if node.package:
                    package_name = node.package.name
                else:
                    return False
                try:
                    out_class = [out_node for out_node in node.children[-1] if
                                 not out_node.name == class_name]
                    inner_class = [inner_node for inner_node in node.children[-1][0].body if
                                   isinstance(inner_node, Tree.ClassDeclaration)]
                    if self.extend_class_methods.__contains__(f'{package_name}.{class_name}'):
                        this_class_methods = self.extend_class_methods.get(f'{package_name}.{class_name}').copy()
                    else:
                        this_class_methods = self.project_pack_dict.get(package_name).get(class_name).copy()
                    for temp_class in out_class:
                        this_class_methods.extend(self.project_pack_dict.get(package_name).get(temp_class.name))
                    for temp_class in inner_class:
                        this_class_methods.extend(
                            self.project_pack_dict.get(package_name).get(f'{class_name}.{temp_class.name}'))
                except:
                    return False
                class_meths_dict, import_dict = self.project_import_dict.get(package_name).get(class_name)
                # if class_name == 'Outer':
                #     print('a')
                # # TODO:为防止最后一个方法失效
                # self.get_api_decs_lists(last_method_node, import_dict, package_name, class_name)
                # 为应对静态变量
                for temp_class_name in class_meths_dict.keys():
                    temp_pack_name = import_dict.get(temp_class_name)
                    if not self.project_pack_dict.__contains__(temp_pack_name):
                        continue
                    static_methods = [method for method in
                              self.project_pack_dict.get(temp_pack_name).get(temp_class_name) if
                              'static' in method[-1]]
                    if static_methods:
                        self.var_dict[temp_class_name] = [f'{temp_pack_name}.{temp_class_name}',
                                                          static_methods]
                self.var_dict.update(self.static_method_dict.copy())
                for key, values in self.static_method_dict.items():
                    self.var_dict[key] = [f'java.lang.{key}', values]

            elif isinstance(node, Tree.InterfaceDeclaration) or isinstance(node, Tree.EnumDeclaration):
                if isinstance(node, Tree.InterfaceDeclaration):
                    temp_class_name = node.name
                    if node in inner_class:
                        temp_class_name = f'{class_name}.{temp_class_name}'
                    # TODO
                    # self.project_structure_dict[self.project_class_hash.get(f'{package_name}.{temp_class_name}')][
                    #     'field'] = node.modifiers
                return False

            elif isinstance(node, Tree.ClassDeclaration):
                temp_class_name = node.name
                if node in inner_class:
                    temp_class_name = f'{class_name}.{temp_class_name}'
                try:
                    self.project_structure_dict[self.project_class_hash.get(f'{package_name}.{temp_class_name}')][
                        'field'] = node.modifiers
                except:
                    pass

            elif isinstance(node, Tree.MethodDeclaration):
                # if node.name == 'testSampleConfiguration':
                #     print('a')
                if self.api_list:
                    params = list()
                    for p in last_method_node.parameters:
                        params.append(p.type.name)
                        # if not p.type.name in basic_type:
                        #     params.append(f'{import_dict.get(p.type.name)}.{p.type.name}')
                        # else:
                        #     params.append(p.type.name)
                    # 应对内部类
                    for i in range(len(last_method_path)):
                        if isinstance(last_method_path[-i - 1], Tree.ClassDeclaration):
                            temp_class_name = last_method_path[-i - 1].name
                            if last_method_path[-i - 1] in inner_class:
                                temp_class_name = f'{class_name}.{temp_class_name}'
                                break
                    temp_contain_methods = self.project_method_hash.get(f'{package_name}.{temp_class_name}')
                    path_method_hash = temp_contain_methods.get(last_method_node.name + '+' + ','.join(params))
                    if not path_method_hash:
                        temp_overload_methods = [temp_method for temp_key, temp_method in temp_contain_methods.items() if temp_key.split('+')
                                                 [0] == last_method_node.name]
                        if temp_overload_methods:
                            path_method_hash = temp_overload_methods[0]
                        # print('a')
                    if None in self.api_list:
                        temp_len = len(self.api_list)
                        if temp_len < 4 or sum(x is not None for x in self.api_list) > 2:
                            self.api_desc = ''
                        else:
                            self.api_list = list(filter(None, self.api_list))
                    if not self.api_desc == '' and path_method_hash:
                        self.all_desc_path.append({
                            'description': self.api_desc,
                            'method': path_method_hash,
                            'api sequences': self.api_list.copy()
                        })
                        self.all_api_list.append(list(self.api_list))
                    self.api_desc = ''

                api_line = node.position.line - 2 - len(node.annotations)
                s = lines[last_node_position:api_line + 1]
                documentation = re.findall('//.*', ''.join(s))
                if documentation:
                    self.api_desc = ''.join(documentation)
                elif node.documentation:
                    self.api_desc = node.documentation
                else:

                    # undo 如果该方法没有注释
                    if '*/' not in lines[api_line]:
                        self.api_desc = ''
                    elif '*/' in lines[api_line] and '/*' in lines[api_line]:
                        self.api_desc = lines[api_line].strip().strip('/').strip('*')
                    else:
                        try:
                            doc_start_num = [i for i in range(1, len(s) + 1) if '/*' in s[-i]]
                            if doc_start_num:
                                self.api_desc = ''.join(s[-(doc_start_num[-1]):])

                        except IndexError:
                            self.api_desc = ''
                self.G.clear()
                self.api_list.clear()
                self.neighbor_dict.clear()
                self.control_node_dict.clear()
                self.last_api = -1
                last_method_node = node
                last_method_path = path

            # elif isinstance(node, Tree.IfStatement) or isinstance(node, Tree.WhileStatement) or isinstance(
            #         node, Tree.ForStatement):
            #     # 如果新的path长度恰好和之前相等，那么就会被覆盖
            #     if not self.api_desc == '':
            #         self.control_node_dict[f'{len(path)},{hash(node)}'] = [node, self.last_api, None, True,
            #                                                                None]

            # 通过path获得局部变量定义，未确定类
            elif isinstance(node, Tree.VariableDeclarator):
                path_len = len(path) - 1
                if isinstance(path[path_len], list):
                    path_len -= 1
                var_class_name = path[path_len].type.name
                if isinstance(node.initializer, Tree.InnerClassCreator):
                    var_class_name = f'{var_class_name}.{node.initializer.type.name}'
                if class_meths_dict.__contains__(var_class_name):
                    pack_name = import_dict.get(var_class_name)
                    self.var_dict[node.name] = [f'{pack_name}.{var_class_name}',
                                                class_meths_dict.get(var_class_name)]
                # 在这里加入java基本类型变量，为参数判断准备
                if var_class_name in java_type:
                    self.var_dict[node.name] = var_class_name

            # 形参，获取变量名及类
            elif isinstance(node, Tree.FormalParameter) and not self.api_desc == '':
                par_class_name = node.type.name
                pack_name = import_dict.get(par_class_name)
                if class_meths_dict.__contains__(par_class_name):
                    self.var_dict[node.name] = [f'{pack_name}.{par_class_name}',
                                                class_meths_dict.get(par_class_name)]

            # 识别new实例化为调用构造器方法，TODO:需要测试
            elif isinstance(node, Tree.ClassCreator) and not self.api_desc == '':
                creator_class_name = node.type.name
                # if creator_class_name == 'Child':
                #     print('a')
                if import_dict.__contains__(creator_class_name):
                    creator_methods = [method for method in class_meths_dict.get(creator_class_name) if
                                       method[0] == creator_class_name]
                    method_decs = get_overload_method_2(node, creator_methods)
                    if method_decs:
                        param_list = [temp_method.split('.')[-1] for temp_method in method_decs[-3]]
                        method_key = method_decs[0] + '+' + ','.join(param_list)
                        temp_pack_class_name = f'{import_dict.get(creator_class_name)}.{creator_class_name}'
                        append_method_hash(method_key, temp_pack_class_name, node, method_decs)

            # 方法调用，须与变量名关联，变量名与类关联，类与包信息关联
            elif isinstance(node, Tree.MethodInvocation) and not self.api_desc == '':
                parse_methodInvocation(node)
            try:
                last_node_position = node.position.line
            except:
                pass

        # TODO:为防止最后一个方法失效
        if last_method_node:
            self.get_api_decs_lists(last_method_node, import_dict, package_name, class_name)


    def get_structure(self, dirname):
        project_structure_dict = dict()
        basic_type = ['byte', 'char', 'short', 'int', 'long', 'float', 'double', 'boolean']

        def get_extend_or_implements(pack_class_name, class_interface, extend_or_implements, package_project,
                                     class_hash): # pass
            if extend_or_implements == 'extend':
                if self.extend_dict.__contains__(pack_class_name):
                    father_class_list = self.extend_dict.get(pack_class_name)
                    if not isinstance(father_class_list, list):
                        father_class_list = [father_class_list]
                    for father_class in father_class_list:
                        father_class_name, father_class_pack = get_pack_name(father_class)
                        #     # TODO:这里可能出现未找到的情况
                        ##### assert
                        extended_hash = self.project_class_hash.get(f'{father_class_pack}.{father_class_name}')
                        if not extended_hash:
                            if project_class_hash.__contains__(father_class):
                                extended_hash = project_class_hash.get(father_class)
                        # if extended_hash is not None: assert type(extended_hash) is str
                        #####
                        if extended_hash:
                            project_structure_dict[class_hash]['extend'].append(extended_hash)
            else:
                if self.implements_dict.__contains__(pack_class_name):
                    for father_class in self.implements_dict.get(pack_class_name):
                        father_class_name, father_class_pack = get_pack_name(father_class)
                        ##### assert
                        implementsed_hash = self.project_class_hash.get(f'{father_class_pack}.{father_class_name}')
                        if not implementsed_hash:
                            if project_class_hash.__contains__(father_class):
                                implementsed_hash = project_class_hash.get(father_class)
                        # if implementsed_hash is not None: assert type(implementsed_hash) is str
                        #####
                        if implementsed_hash:
                            project_structure_dict[class_hash]['implement'].append(implementsed_hash)

        def get_method(package_name, class_name, package_project, package_path, class_hash):
            # if class_name == 'QueueBuilder':
            #     print('a')
            method_list = self.project_pack_dict.get(package_name).get(class_name)
            method_dimensions_list = self.project_var_dimensions.get(f'{package_name}.{class_name}')
            if not method_list or not method_dimensions_list:
                return None
            if len(method_dimensions_list) - len(method_list) != 0:
                # class_pash = f'{self.pack_path_dict.get(package_name)}/{class_name}\n'
                # write_file('errorfile.txt', class_pash)
                # print('1')
                return None
            # assert len(method_dimensions_list)-len(method_list) == 0
            # if len(method_list) > 0:
            #     have_construt_flag = 0 if method_list[0][0] == class_name.split('*')[-1] else 1
            for i in range(len(method_list)):
                method = method_list[i]
                method_dimensions = method_dimensions_list[i]
                # if method[0] == 'overflow':
                #     print('a')
                # try:
                #     method_dimensions = method_dimensions_list[i + have_construt_flag]
                # except IndexError:
                #     return None
                # TODO:构造器
                params = []
                for param in method_dimensions[0]:
                    if param[0] in basic_type:
                        params.append([f'basictype${param[0]}', param[1]])
                    else:
                        param_class_name, param_class_pack = get_pack_name(param[0])
                        if self.pack_path_dict.__contains__(param_class_pack):
                            # param_path = self.pack_path_dict.get(param_class_pack).removeprefix(split_path)
                            param_hash = f'class${package_project}${param_class_pack}${param_class_name}'
                            params.append([param_hash, param[1]])
                        # TODO

                        elif self.pack_dict.__contains__(param_class_pack):
                            params.append(
                                [self.project_class_hash.get(f'{param_class_pack}.{param_class_name}'), param[1]])
                        elif project_class_hash.__contains__(f'{param_class_pack}.{param_class_name}'):
                            params.append(
                                [project_class_hash.get(f'{param_class_pack}.{param_class_name}'), param[1]])
                param_hash = ''
                for param in params:
                    # if param[1] > 0:
                    #     print('a')
                    param_hash += param[0].split('$')[-1]
                    param_hash += '[]'*param[1]
                    param_hash += ','
                param_hash = param_hash.rstrip(',')
                # if class_name == 'AmqpMessageReturnedException' and method[0] == 'getReturnedMessage':
                #     print('a')
                return_hash = ['basictype$void', 0]
                if method_dimensions[1][0] and method_dimensions[1][0] not in basic_type:
                    return_class_name, return_class_pack = get_pack_name(method_dimensions[1][0])
                    if self.pack_dict.__contains__(return_class_pack) or self.project_pack_dict.__contains__(return_class_pack):
                        return_class_hash = self.project_class_hash.get(f'{return_class_pack}.{return_class_name}')
                        if return_class_hash:
                            return_hash = [return_class_hash, method_dimensions[1][1]]
                        # else:
                        #     write_file('errorfile.txt', f'find class {return_class_pack}.{return_class_name} failed\n')
                elif method_dimensions[1][0] in basic_type and not method_dimensions[1][0] == 'void':
                    return_hash = [f'basictype${method_dimensions[1][0]}', method_dimensions[1][1]]
                elif not method_dimensions[1][0]:
                    return_hash = 'None'
                else:
                    return_hash = ['basictype$void', 0]
                params_str = ','.join(method[-3])
                # 去除返回值
                method_hash = f'method${package_project}${package_name}${class_name}${method[0]}({param_hash})'
                self.project_method_hash[f'{package_name}.{class_name}'][method[0] + '+' + param_hash.replace('[]','')] = method_hash
                project_structure_dict[method_hash] = {
                    'type': 'method',
                    'project': package_project,
                    'path': package_path,
                    'package': package_name,
                    'class': class_name,
                    'method': method[0],
                    'field': method[-1],
                    'parameter': params,
                    'return': return_hash,
                    'hash': method_hash
                }
                project_structure_dict[class_hash]['contain method'].append(method_hash)

        def get_var(package_name, class_name, package_project, package_path, class_hash):
            try:
                var_decs_list = self.field_var_dict.get(package_name).get(class_name)
            except:
                return None
            if not var_decs_list:
                return None
            var_hash_list = []
            for var_decs in var_decs_list:
                project_structure_dict[var_decs[0]] = {
                    # TODO
                    'type': 'member',
                    'project': package_project,
                    'path': package_path,
                    'package': package_name,
                    'class': class_name,
                    'member': var_decs[3],
                    'return': var_decs[1],
                    'field': var_decs[2],
                    'hash': var_decs[0]
                }
                var_hash_list.append(var_decs[0])
            project_structure_dict[class_hash]['contain member'] = var_hash_list

        def package_class_structures():
            for package_name in self.project_pack_dict.keys():
                package_project = dirname.split('/')[-1]
                package_path = self.pack_path_dict.get(package_name).removeprefix(split_path)
                package_hash = f'package${package_project}${package_name}'
                project_structure_dict[package_hash] = {
                    'type': 'package',
                    'project': package_project,
                    'path': package_path,
                    'package': package_name,
                    'contain class': [],
                    'hash': package_hash
                }
                interface_names = []
                if self.project_pack_interface_dict.__contains__(package_name):
                    interface_names = self.project_pack_interface_dict.get(package_name).keys()
                    for interface_name in interface_names:
                        interface_hash = self.project_class_hash.get(f'{package_name}.{interface_name}')
                        import_class_hashes = []
                        try:
                            for import_class_name, import_class_pack in \
                            self.project_import_dict.get(package_name).get(interface_name)[1].items():
                                # todo
                                # if not self.project_class_hash.get(f'{import_class_pack}.{import_class_name}'):
                                #     print('a')
                                import_class_hashes.append(
                                    self.project_class_hash.get(f'{import_class_pack}.{import_class_name}'))
                        except TypeError as e:
                            print(e)
                        self.project_method_hash[f'{package_name}.{interface_name}'] = dict()
                        project_structure_dict[interface_hash] = {
                            'type': 'interface',
                            'project': package_project,
                            'path': package_path,
                            'module': 'None',
                            'package': package_name,
                            'field': list(self.project_class_field.get(f'{package_name}.{interface_name}')),
                            'description': '',
                            'extend': [],
                            'implement': [],
                            'contain method': [],
                            'contain class':[],
                            'import': import_class_hashes,
                            # TODO
                            'contain member': [],
                            'hash': interface_hash
                        }
                        project_structure_dict.get(package_hash).get('contain class').append(interface_hash)
                        get_extend_or_implements(f'{package_name}.{interface_name}', 'interface', 'extend',
                                                 package_project,
                                                 interface_hash)
                        get_method(package_name, interface_name, package_project, package_path, interface_hash)
                        project_structure_dict[interface_hash]['extend'] = list(filter(lambda x: x != None, project_structure_dict[interface_hash]['extend']))
                        project_structure_dict[interface_hash]['implement'] = list(filter(lambda x: x != None, project_structure_dict[interface_hash]['implement']))
                for class_name in self.project_pack_dict.get(package_name).keys():
                    if class_name in interface_names:
                        continue
                    class_hash = self.project_class_hash.get(f'{package_name}.{class_name}')
                    if not class_hash:
                        continue
                    import_class_hashes = []
                    try:
                        for import_class_name, import_class_pack in \
                        self.project_import_dict.get(package_name).get(class_name)[1].items():
                            temp_class_hash = self.project_class_hash.get(f'{import_class_pack}.{import_class_name}')
                            if not temp_class_hash:
                                temp_class_hash = 'unknown'
                            if temp_class_hash:
                                import_class_hashes.append(temp_class_hash)
                    except:
                        pass

                    self.project_method_hash[f'{package_name}.{class_name}'] = dict()
                    project_structure_dict[class_hash] = {
                        'type': 'class',
                        'project': package_project,
                        'path': package_path,
                        'module': 'None',
                        'package': package_name,
                        'field': list(self.project_class_field.get(f'{package_name}.{class_name}')),
                        'description': '',
                        'extend': [],
                        'implement': [],
                        'contain method': [],
                        'import': import_class_hashes,
                        # TODO
                        'contain member':[],
                        'hash': class_hash
                    }
                    get_var(package_name, class_name, package_project, package_path, class_hash)
                    get_extend_or_implements(f'{package_name}.{class_name}', 'class', 'extend', package_project,
                                             class_hash)
                    get_extend_or_implements(f'{package_name}.{class_name}', 'interface', 'implement', package_project,
                                             class_hash)
                    project_structure_dict.get(package_hash).get('contain class').append(class_hash)
                    get_method(package_name, class_name, package_project, package_path, class_hash)

        package_class_structures()
        return project_structure_dict

    # @profile
    def parse(self, dirname):
        package_project = dirname.split('/')[-1]
        self.get_project_api(dirname)
        self.get_re_param(dirname)

        self.get_extend_methods()
        self.project_structure_dict = self.get_structure(dirname)
        # write_json('./error/extend_error_parse.json', self.extend_error_list, 'a')
        write_json(f'./structure_file/{package_project}.structure.json', self.project_structure_dict, 'w')
        for maindir, subdir, file_name_list in os.walk(dirname):
            maindir = maindir.replace('\\', '/')
            for java_file in file_name_list:
                # try:
                if java_file.endswith('.java'):
                    # try:
                    #     self.parse_java_file(java_file, maindir)
                    # except Exception as e:
                    #     print(e)
                    #     pass
                    self.parse_java_file(java_file, maindir)
        for i in range(math.ceil(len(self.all_desc_path) / 10000)):
            write_json(f'./json_file/{package_project}.{i}.dataset.json', self.all_desc_path, 'w')

        print(f'新增{len(self.all_desc_path)}条数据')
        self.dump_pkl_notCover('graph.pkl', self.all_api_list)
        self.dump_pkl_notCover('graph.pkl', self.all_neighbor_dict)
        return self.extend_error_list


def write_file(path, str):
    with open(path, 'a') as file:
        file.write(str)


def write_json(path, structure_dict, mode):
    json_str = json.dumps(structure_dict, indent=4)
    with open(path, mode) as json_file:
        json_file.write(json_str)


if __name__ == '__main__':

    # 运行测试文件
    # open('./error/errorfile.txt', 'w').close()
    # maindir = 'C:/Users/wkr/Desktop/java_parser/clicy-master'
    # basic_type = ['char', 'short', 'int', 'long', 'float', 'double', 'boolean', 'void', 'byte']
    # project_class_hash = load_json('./doc_project_dict/project_class_hash.json')
    # all_doc_project_dict = load_json('./doc_project_dict/all_doc_project_dict.json')
    # all_extend_error_dict = dict()
    # my_parse = AST_parse()
    # my_parse.parse(maindir)
    # exit()


    open('./error/errorfile.txt', 'w').close()
    open('./error/extend_error_parse.json', 'w').close()
    open('./error/innerclass_file.txt', 'w').close()

    # 处理github项目
    file_num = 0
    # for whw，此处需要修改为spring-file本地路径
    # maindir = 'E:/java_project/spring-file-oldbranch'
    maindir = 'F:/java_project/spring-file-oldbranch'
    # maindir = 'F:/java_parser/clicy-master'
    # maindir = 'C:/Users/wkr/Desktop/java_parser/clicy-master'
    file_list = os.listdir('./structure_file_fromhw')
    basic_type = ['char', 'short', 'int', 'long', 'float', 'double', 'boolean', 'void', 'byte']
    project_class_hash = load_json('./doc_project_dict/project_class_hash.json')
    all_doc_project_dict = load_json('./doc_project_dict/all_doc_project_dict.json')
    all_extend_error_dict = dict()
    # my_parse = AST_parse('spring-amqp-main.structure.json')
    # all_extend_error_dict['spring-amqp-main'] = my_parse.parse(f'F:/java_project/spring-amqp-2.4.x')
    # exit()
    for subdir in file_list:
        subdir = subdir.removesuffix('-main.structure.json')
        file_num += 1
        print(f'开始解析第{file_num}个文件{subdir}')
        if file_num in {7, 12}:
            continue
        print('当前时间为：{}'.format(time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(time.time()))))
        if os.path.isdir(f'{maindir}/{subdir}') or subdir.endswith('.java'):
            my_parse = AST_parse()
            all_extend_error_dict[subdir] = my_parse.parse(f'{maindir}/{subdir}')
    write_json('./error/extend_error_parse.json', all_extend_error_dict, 'w')
    new_no_class = []
    for i in no_class:
        if i not in new_no_class:
            new_no_class.append(i)
            write_file('./error/innerclass_file.txt', f'{i}\n')
    exit()



# undo 方法间的调用顺序  do
# undo 返回值，参数问题  java.util.Arrays.asList(T...)


