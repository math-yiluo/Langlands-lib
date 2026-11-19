# Additive triangular coordinates for complex Godement sections

An upper unipotent matrix times the positive diagonal with entries
`exp (y j)` has diagonal `exp (y j)` and strictly upper entries obtained
by multiplying column `j` by `exp (y j)`. The map `scaleUpperEntries`
implements that change of variables. Real Lebesgue measure on each
complex entry transforms by the inverse square of the column factor.
The strictly upper entries in column `j` are indexed by `Fin j.val`,
so the product measure transforms by the product of the inverse
squares to the powers `j.val`. This gives the upper-triangular
version of the Jacobian in Jacquet's triangular reduction of the
Godement integral.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, p. 44](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
