# Norm-one approximation by classical cuspidal functions

`AdelicNormOneClassicalCuspidalDensityStatement` concerns an affine locally
finite-type connected reductive group `G` over a number field `F`. It uses
a supplied smooth relative dimension, a compact subgroup of `G(F∞)` and a
closed matrix embedding of positive size. The input is a continuous,
rationally invariant function which is smooth on each archimedean slice
and is fixed on the right by one common open subgroup at the finite
adeles. Its normalized periods along all proper rational parabolics vanish.
Every archimedean real derivative word has a height bound with its own
constant and a common nonnegative exponent, including the empty word.

For each positive error the statement asks for a cuspidal function
satisfying `IsAutomorphicFunctionOn` for the specified compact subgroup and
embedding, with the same type of uniform directional height growth. The
`L²` seminorm of the difference of the two restrictions to
`G(F) \ G(𝔸_F)¹` with quotient Haar measure must be smaller than the error.

Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
I.3.4, p. 46, uses classical cusp density on the quotient by `A_G G(F)`
after smoothing. In the number-field splitting of Bernstein–Lapid,
*On the meromorphic continuation of Eisenstein series* (2024), §6.2, p. 201,
the positive split-central factor is removed by passing to the norm-one
subgroup. Section 6.2, (6.8), p. 202, uses this norm-one quotient for the
Levi tests. The uniform derivative growth condition is the one used for
adelic relative rapid decay. Its compact-convolution origin for classical
forms is described in Mœglin–Waldspurger I.2.5 and I.2.17, pp. 26–27 and 37–39.
