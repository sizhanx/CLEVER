def lib(x):
    if x > 10:
        return 12
    else:
        return x+1

def yi1(x):
    if x > lib(x):
        return x
    else:
        return lib(x)
