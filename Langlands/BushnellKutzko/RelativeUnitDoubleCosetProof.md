# Relative unit double cosets by simultaneous interpolation

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Mathematics Studies 129 (1993), Theorem (1.6.1), printed
p. 47 (PDF p. 59). The retained source `bushnell-kutzko-1993-admissible-dual-gln`
has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`relativeUnitDoubleCoset` proves `RelativeUnitDoubleCosetStatement` for a
normalizing field `E = F[β]`. Suppose `z = u y v` with `y` and `z` in
`Aut_E(V)` and `u` and `v` in the ambient positive-depth unit subgroup.
Rearrange this equation as `(1 + a) z = y (1 + b)`, where `a = u⁻¹ − 1`
and `b = v − 1` both lie in the indicated depth of the base filtration.

The relative chain has the same lattices as the base chain. The argument in
`exists_relative_corrections` uses a common splitting basis over `E` for
this chain and its translate by `z⁻¹`. It interpolates `a z` and `b` on
that basis to produce `E`-linear corrections `a'` and `b'` at the original
depth with `(1 + a') z = y (1 + b')`. Positive depth makes both corrected
terms units, now in the relative unit group. Consequently `z` is in the
relative double coset. The reverse inclusion uses that the relative units
lie in both the ambient unit group and the centralizer.
