def lib1(x):
    if x < 0:
        return -x
    counter = 0
    while x > 0:
        x += 1
        counter += 1
    return counter

def pos2(x):
    if (x < 0):
        return lib(x)
    return -x
