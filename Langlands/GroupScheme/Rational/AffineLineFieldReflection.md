# Reflection of affine-line constancy through field extension

This internal descent lemma is a formal consequence of faithfully flat
descent of morphism equalities. It requires no smoothness, affineness,
connectedness, unipotence, algebraicity, or separability assumption.

`AffineLine.baseChangeMap` extends an actual affine-line morphism along
an arbitrary scheme base morphism and identifies its source with the
affine line over the new base using the canonical comparison.

`HasConstantAffineLineMaps.of_fieldExtension` states that if the actual
scalar extension of a group scheme over a field has only constant
affine-line morphisms, then the original group scheme has the same
property. The maps quantified over are all scheme morphisms.

The proof pulls back an arbitrary ground-field affine-line morphism and
uses the canonical comparison with the affine line over the extension.
Constancy identifies this morphism with its value at zero. The published
zero-section compatibility transports that equality through the
comparison, and faithful fpqc pullback reflects the equality to the
ground field. The constant value is the original morphism evaluated at
the ground-field zero section.
