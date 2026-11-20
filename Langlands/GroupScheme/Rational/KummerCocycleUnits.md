# Kummer cochains on a finite Galois coefficient field

For a field extension `E/F`, `KummerCocycle.rootValue` is the unit `σ(z) / z`
in the roots-of-unity subgroup when `z^n` comes from a base-field unit. Its
underlying values satisfy the crossed cocycle law. When `E/F` is finite
Galois, Hilbert 90 gives such a unit `z` for every crossed unit cocycle whose
values have `n`-th power one, and fixed-field descent sends `z^n` to `F`.

`exists_root_compare` compares two such cochains on a common coefficient
field. Write `ι` for the unit map from `F` to `E` and take units satisfying
`x^n = ι(a)`, `y^n = ι(b)`, and `a = b * q^n`. The quotient of the radicals,
corrected by the lifted base unit, is `t = x / (y * ι(q))`. It satisfies
`t^n = 1` and `σ(t)/t = (σ(x)/x)/(σ(y)/y)` for every `σ`. This internal
comparison gives the cochain used to match local central corrections.
