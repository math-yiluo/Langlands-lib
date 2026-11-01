# Positive integral ample coefficient from an actual coherent cut

`integral_lineBundleEulerPolynomial_coeff_pos` proves
`IntegralAmpleEulerCoefficientStatement`.

The exact-dimensional ample section theorem supplies a positive tensor
exponent `n`, a section whose generation open is nonempty, and its actual
categorical cokernel `Q`. The cokernel is quasi-coherent with finite affine
sections, and its closed stalk support has dimension exactly `d`.

The equivalence between strict support bounds and the topological dimension
of closed stalk support shows that `Q` satisfies bound `d + 1` and fails bound
`d`. The assumed coherent coefficient criterion in dimension `d` therefore
gives strict positivity of coefficient `d` of its actual Euler polynomial.

The actual section-cokernel coefficient identity identifies that coefficient
with `(d + 1) * n` times coefficient `d + 1` of the structure-module line-bundle
Euler polynomial. Both natural factors are positive. Cancelling their positive
rational product proves the stated strict positivity, including the case
`d = 0`.

This internal proof implements Worker 689's induction-step interface and
reuses Worker 689's exact-dimensional coherent cut together with Worker 1013's
section-cokernel coefficient identity. The lower-dimensional criterion remains
the explicit induction hypothesis. This lemma alone does not prove the general
criterion or the full polarized finite-flat rank statement.
