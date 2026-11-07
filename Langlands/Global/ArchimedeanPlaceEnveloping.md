# Actual place enveloping algebras and global retractions

For any field `F : Type u` and natural rank `n`, this module constructs
the actual enveloping algebras of the archimedean place Lie algebras and
embeds them into the original global enveloping algebra. All ranks,
including zero, and the arbitrary field universe are retained.
No number-field hypothesis is required.

`RealPlaceEnvelopingAlgebra n` is the universal enveloping algebra over
the complex numbers of the complexified real matrix Lie algebra.
`ComplexPlaceEnvelopingAlgebra n` first views the entire complex matrix
Lie algebra as real, then complexifies it and forms its complex universal
enveloping algebra. Thus both real directions at a complex place remain.
These algebras depend only on the rank and the indicated local scalar
field, rather than on an auxiliary model for a representation. Their
generator maps are the actual universal enveloping generators.

`realPlaceComplexLieProjection` and `complexPlaceComplexLieProjection`
extend the existing actual real Lie coordinate projections by complex
scalars. Their pure tensor formulas retain the first scalar factor.
Tensor induction and the existing projection/insertion formulas prove
that each such map retracts the corresponding actual place Lie inclusion.

`realPlaceEnvelopingInclusion` and `complexPlaceEnvelopingInclusion` are
the universal enveloping lifts of the actual place Lie inclusions,
followed by the original global enveloping generator. Their formulas on
every generator agree with the original inserted global Lie generator.
The enveloping projections similarly lift the actual complexified Lie
coordinate projections, followed by the appropriate local generator.

The composition of each enveloping projection with its corresponding
inclusion is the identity on the entire local enveloping algebra.
Universal enveloping extensionality reduces this assertion to the
proved retraction identity on Lie generators. Evaluating that algebra
homomorphism identity proves the pointwise retraction formula, injectivity
of both actual inclusions and surjectivity of both actual projections.
No Poincaré–Birkhoff–Witt premise or supplied injectivity hypothesis is
needed for these split inclusions.

This is an internal construction from `ArchimedeanPlaceLie` and pinned
Mathlib's complex scalar extension and universal enveloping algebra.
It uses no new assertion from original literature, topology or
normalization. It constructs neither irreducible local automorphic
factors nor a Langlands attachment.
