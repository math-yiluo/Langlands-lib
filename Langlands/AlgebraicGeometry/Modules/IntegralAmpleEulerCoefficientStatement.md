# Integral ample Euler coefficient positivity from lower dimension

`IntegralAmpleEulerCoefficientStatement` states an induction step in arbitrary
universe `u`. Assume `AmpleCoherentEulerCoefficientInDimension d`, the coherent
coefficient criterion in support dimension at most `d`. For every
integral Noetherian separated scheme proper over a field, of topological Krull
dimension exactly `d + 1`, and every ample actual line bundle `L`, coefficient
`d + 1` of `lineBundleEulerPolynomial f L (d + 1)` is strictly positive.

The polynomial is the existing Newton reconstruction of the actual
structure-module Euler sequence. The induction hypothesis applies to actual
coherent sheaves and detects their strict support bounds. It is an explicit
premise of this induction step; the statement does not assert the criterion
in every dimension or the full smooth proper Euler-polynomial theorem.

This is an internal supporting statement for the ample coefficient induction
and the polarized finite-flat rank theorem. Its proof,
`integral_lineBundleEulerPolynomial_coeff_pos` (module
`IntegralAmpleEulerCoefficientProof`), follows the exact-dimensional section
route and uses the actual section-cokernel coefficient identity
`Picard.sectionCokernelEulerCoefficient`. Its
provenance is these existing geometric and polynomial constructions.
