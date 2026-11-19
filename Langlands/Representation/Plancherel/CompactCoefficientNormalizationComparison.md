# Change of compact Haar normalization for product-induced coefficients

`CompactInduction.coefficientCompactNormalizationScalar` is the normalized
Haar average on the first compact subgroup of the square of the Iwasawa
weight for the second. For two compact open Iwasawa factors of the same
parabolic, `CompactInduction.exists_pos_coefficientMap_eq_mul_of_compact`
uses this positive real number to compare the two probability-normalized
coefficient maps. The first coefficient equals the scalar times the second
at every group point. The scalar is independent of the inducing admissible
representation and the input vector in the common product-induced carrier.

The proof applies the real compact average comparison
`HarishChandraSchwartz.integral_compact_eq_mul` to the real and imaginary
parts of a complex covariant integrand. On an induced pure tensor, the
diagonal integrand is the pairing of the contragredient induced function and
the translated vector-valued induced function. It is locally constant by
`Induction.bilinearPairing_isLocallyConstant` and transforms by the
parabolic modulus by `Induction.dualPairing_covariant` and
`closedHalfCharacter_mul_self`. The compact probability coefficient formula
identifies the resulting two integrals with the desired coefficients.
Tensor-product induction and linearity extend the identity to every vector.
The Iwasawa weight is continuous and strictly positive on the first compact
subgroup, so its squared integral over Haar probability is strictly positive.

This is a derived normalization comparison for using a compact subgroup
with compatible standard-Levi intersections in the estimates for
Waldspurger VI.3.1. The underlying induced function and group evaluation
point are exactly the same in both normalizations.
