# Fixed norms on the common-Levi compact pictures

`compactNormModel` provides the complex normed carrier obtained from
normalized induction with its positive compact Haar form. The equivalence
uses the inverse untwisted compact restriction. `compactNormModel_inner`
computes the inner product on that carrier by the literal Haar probability
of the compact group. Both evaluations in the integrand are unchanged by
restriction, so `compactNormModel_twist_inner` identifies the same fixed
form with the pairing at every unitary twist.

`exists_compactPictureDualPairing_norm_bound` extends a fixed test section
of the smooth dual from the compact picture and uses `integralDualEquiv`
to obtain a smooth functional of the original normalized induction.
Admissibility of this induction and `InvariantPositiveForm.smoothDualEquiv`
represent the functional by an inducing vector for its invariant form.
Cauchy–Schwarz bounds the compact pairing, with the norm of that representing
vector as the constant. `integralDualEquiv_pairing` identifies the test
functional with the compact probability integral used in the adjunction.

These are the compact Hermitian products and dual pairings of Waldspurger
IV.1(11), printed p. 283, and V.2, printed pp. 293–294. Source
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

`exists_compactForward_similitude` uses `genericForwardSimilitude` on the
irreducible twisted induction. `forward_compact_square` identifies its
forward operator with the compact continuation. The fixed-form comparison
then gives the square root of the positive similarity factor as the norm
scale. `exists_uniform_compactForward_inverse_bound` uses the fixed nonzero
value from `continuedPair_forwardTest_eq` and bounds that pairing by the
norm of its output. This gives a parameter-independent positive lower bound
on the forward norm scale, hence the uniform inverse estimate.
