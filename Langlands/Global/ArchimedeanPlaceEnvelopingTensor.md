# Actual commuting place enveloping algebras and tensor maps

For any field `F : Type u` and natural rank `n`, this module proves that
the actual local enveloping subalgebras in the global archimedean
enveloping algebra commute at distinct places. It constructs their
two-factor tensor-product algebra maps. All ranks and the arbitrary field
universe are retained; no number-field hypothesis is needed.

The real and complex place Lie inclusions insert matrices with zero at
all other coordinates. Coordinate evaluation therefore proves that their
Lie bracket vanishes at distinct places. The same-type statements retain
the explicit hypothesis that the two places differ. A real place and a
complex place are already different types of place and require no
inequality hypothesis. Tensor induction in both complexified directions
extends each zero-bracket identity, retaining the full underlying real
matrix Lie algebra at a complex place.

The original global enveloping generator sends these zero brackets to
zero commutators. A private universal enveloping argument extends
commutation from all Lie generators to all algebra elements: quotient
induction selects a tensor-algebra representative, then tensor-algebra
induction handles scalars, generators, products and sums. Scalars commute
by the actual complex algebra structure, and commutation is preserved
under products and sums. Applying this argument in both local algebras
proves commutation of their entire actual images.

`realPlacesEnvelopingTensorMap` and
`complexPlacesEnvelopingTensorMap` multiply the actual included elements
at two distinct places of the same type.
`realComplexPlacesEnvelopingTensorMap` does the same for a real and a
complex place. The proved image-commutation law supplies the intrinsic
condition for Mathlib's tensor-product algebra lift. These are unital
complex algebra homomorphisms into the original global enveloping
algebra, with explicit pure-tensor formula equal to the product of the
two actual included elements.

This is an internal construction from `ArchimedeanPlaceEnveloping`, the
actual place Lie coordinates and generators, and pinned Mathlib's
universal enveloping quotient and algebra tensor-product lift. It
introduces no source assertion, topology or normalization.

No injectivity or surjectivity of these two-factor tensor maps is
asserted. The module constructs neither a tensor decomposition of an
automorphic representation nor irreducible local factors or a Langlands
attachment.
