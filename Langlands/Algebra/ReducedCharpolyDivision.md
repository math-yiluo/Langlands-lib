# Reduced characteristic polynomials in a division algebra

Let `K` be a field and `D` a finite-dimensional central division algebra
in the same arbitrary universe. The published theorem
`Langlands.CentralDivision.aeval_reducedCharpoly` proves that the canonical
reduced characteristic polynomial annihilates each element of `D`.
Its statement and proof are retained from `DivisionReducedCharpoly`:
Cayley–Hamilton for left multiplication makes a positive power of the
reduced-polynomial value zero, and a division ring has no nonzero nilpotents.

The reviewed degree-two helpers from `Quaternionic.AlternatingConjugation`
are placed here with the same names and hypotheses.
`Langlands.CentralSimple.reducedCharpoly_coeff_zero_two` identifies the
constant coefficient with the reduced norm of `1 ⊗ a`, using evaluation at
zero and the norm of the scalar `−1`.
`Langlands.CentralSimple.reducedCharpoly_eq_quadratic` expands the monic
polynomial as `X² + c₁ X + Nrd(a)`. Both require reduced degree two.
All three identities hold in every characteristic. The division-algebra
degree bounds and quaternionic involution constructions reuse this module.
