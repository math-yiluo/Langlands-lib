# Determinant normalization and special-linear geometry

This internal construction proves smoothness and field connectedness of the
actual group scheme `SpecialLinear.groupScheme`. Its coordinate algebra is the
polynomial ring in matrix entries modulo the single equation `det - 1`, as
defined in `SpecialLinear`. Fix a finite index with decidable equality and a
chosen pivot `p`. The matrix construction permits independent universes for the
index and coefficient rings. The coordinate and scheme constructions use a
finite index in `Type` and an arbitrary base-ring universe. No field or
characteristic restriction is needed for normalization or smoothness.

`pivotDiagonal p a` is the invertible diagonal matrix with the unit `a` in
position `p` and ones elsewhere. Its inverse has `a⁻¹` in that position, and
its determinant is `a`. The construction commutes with every coefficient
homomorphism. `normalize p g` is the actual determinant-one matrix

`D(p, det(g)⁻¹) * g`.

The determinant identity proves membership in the special linear group.
`toGL_normalize` identifies its image in the general linear group with this
product. `normalize_map` proves coefficient naturality, and `normalize_toGL`
proves that normalization fixes every determinant-one matrix. Normalization is
a map of the underlying matrix varieties; no group homomorphism property is
asserted.

`restrictCoordinates` classifies the inclusion of the universal special-linear
matrix. `normalizeCoordinates` classifies the normalization of the universal
general-linear matrix. Naturality of normalization and its identity on
determinant-one matrices show that restriction composed with normalization
pullback is the identity algebra map. Thus the special-linear coordinate ring
is an explicit algebra retract of the existing general-linear coordinate ring.

`finitePresentation_coordinateRing` uses the single defining equation.
`coordinateRing_smooth` uses the existing smoothness of the general-linear
coordinate ring and `Algebra.FormallySmooth.of_split`. If `f` is restriction
and `j` is normalization pullback, compose `j` with the quotient by
`ker(f)²`. The identity `f ∘ j = id` gives the section required by that
formal-smoothness criterion. Combining formal smoothness and finite
presentation proves algebraic smoothness. The affine spectrum criterion then
proves `smooth_groupScheme` for the actual structure morphism.

`comap_normalizeCoordinates_surjective` gives a preimage of every prime by
comapping it along restriction. The composite identity proves this is a
preimage under normalization pullback. Over a field, the general-linear
coordinate ring is a domain by the existing determinant-localization
description, so its spectrum is connected. The continuous surjective
normalization map proves `connectedSpace_groupScheme`.

The provenance is internal: the pivot matrix, determinant identities,
representing-coordinate retract and the stated smoothness and topological
criteria give the entire argument. The module reuses the established
general-linear geometry rather than assuming special-linear geometry.
It does not yet prove triviality of the unipotent radical, geometric
reductivity, classification of local rank-one groups, or the unrestricted
local Kneser–Tits theorem.
