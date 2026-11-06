# Intrinsic normalized block constant terms and the original matrix integral

This internal comparison uses the actual general-linear group scheme over an
arbitrary number field, its actual two-block unipotent subgroup with `a + b = n`,
and the intrinsic `normalizedRationalQuotientHaarMeasure` on its principal-image
rational quotient. It retains the explicit hypothesis that the additive adele
quotient is compact. Empty blocks are allowed.

The quotient carries its inherited measurable structure. The proved
`rationalQuotientBorelSpace` identifies this structure with its Borel sigma
algebra. The two private transport lemmas eliminate this proved equality of
measurable spaces and apply the identity pushforward law. The intrinsic measure
comparison `normalizedRationalQuotientHaarMeasure_eq` then identifies this
pushforward with the original `rationalQuotientMeasure`. Neither transport
assumes that the two measurable spaces are definitionally equal.

The integrability equivalence follows by this explicit identity transport and
the existing original block integrability comparison. The original compact
matrix convergence theorem therefore proves
`hasConvergentConstantTerm_generalLinearBlock_intrinsic` on the full continuous
rational-invariant space. This separately establishes absolute Bochner
integrability at every actual ambient point.

`constantTerm_generalLinearBlock_intrinsic` transports the intrinsic integral
to the original Borel quotient integral, then applies the existing equality
with the original matrix constant term. The ambient function is the unchanged
`continuousGeneralLinearEquiv` image and the ambient argument is the existing
actual adelic point homeomorphism image. There is no additional scalar factor
or assumed measure-comparison premise.

`intrinsicGeneralLinearBlockConstantTermLinearMap` bundles the intrinsic integral
as a complex linear map on the full continuous space. The existing compact
quotient linearity theorem applies with the proved intrinsic probability
measure. Its evaluation is the original matrix constant term. Positive ambient
right translation follows from the generic integral law; left invariance under
actual two-block subgroup points follows from the comparison and the existing
original normalized block invariance.

Finally, `hasVanishingConstantTerm_generalLinearBlock_intrinsic_iff` compares
intrinsic convergence and vanishing with original matrix block vanishing at
every adelic argument. The previously proved convergence supplies the forward
analytic condition independently of the integral value, and surjectivity of
the actual ambient point homeomorphism changes the argument quantifier.

The provenance is internal composition of the proved intrinsic normalized
measure identity with the existing actual block constant-term comparison.
The intrinsic measure belongs to the simultaneous subgroup-Haar and quotient
normalization established in `GeneralLinearBlockIntrinsicMeasure`; that
module's exact counting-measure Weil compatibility is retained. This unit
does not classify rational parabolics, identify their unipotent radicals, prove
all-proper cuspidality, establish general reductive finite volume or reduction
theory, or supply a growth, smoothness or Hilbert-space comparison.
