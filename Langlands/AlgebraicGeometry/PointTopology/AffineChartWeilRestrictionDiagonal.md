# Closed diagonal charts for the actual Weil model

Worker 208 derives these intrinsic construction laws for the existing glued
Weil scheme. They support the finite type separated Weil model used in Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10. They do not establish the full adelic comparison.

A and B are commutative rings in the same arbitrary universe, B is finite
projective over A, and Y is the existing actual scheme over Spec B, locally of
finite type. Given two actual affine opens U and V with affine intersection,
`affineChartWeilRestrictionDiagonalChartMap` is the map from the Weil scheme of
that original intersection to the product of its two original Weil charts over
Spec A. Its two projections are the existing Weil maps of the original
inclusions. The construction itself requires only the explicit affine
intersection hypothesis.

If Y is separated over Spec B, the original map U intersection V into
U times over Spec B V is a closed immersion: it is the original intersection
isomorphism followed by the base change of Y's closed diagonal. Affine Weil
restriction preserves that closed immersion. The exact projection identities
of the original relative product comparison identify the preserved map with the
constructed diagonal chart map, proving that map is closed.

Separatedness of Y also implies that any two original affine opens have affine
intersection, since Spec B is separated. The actual Weil chart overlap
comparison identifies the pullback of the two chart inclusions with the Weil
scheme of their original intersection. Its exact projection identities show
that the induced map from this overlap to the relative product is precisely
the closed diagonal chart map, up to the given source isomorphism.

Finally the existing full affine Weil chart cover covers the actual glued
scheme. The target is the original affine Spec A. The affine locality theorem
for the diagonal and the affine characterization of closed immersions prove
that its structural morphism is separated. This is an intrinsic law of the
same existing model, and neither its separatedness nor its diagonal's
closedness is an input. No compactness, finite affine neighborhood,
quasi-projectivity, separability, reducedness or Noetherian hypothesis is used.
