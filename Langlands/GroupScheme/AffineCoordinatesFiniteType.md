# Finite type of affine group coordinates

This internal supporting construction defines and registers the instance
`AffineCoordinates.algebraFiniteType`: for an actual affine group scheme `G`
over `Spec R`, local finite type of `G.X.hom` implies
`Algebra.FiniteType R (AffineCoordinates.algebra G)`. The commutative base ring
and its universe are arbitrary. No smoothness, field, reductivity, or splitness
hypothesis is used.

The proof takes the underlying relative-spectrum isomorphism of
`AffineCoordinates.coordinateCogroupIso G`. Local finite type is preserved by
composing its underlying scheme isomorphism with the structure morphism of `G`.
Pinned Mathlib's `HasRingHomProperty.Spec_iff` converts this property for a
spectrum morphism into finite type of its algebra map, and
`RingHom.finiteType_algebraMap` gives the algebra instance.

When the consumer starts with `IsAffineHom G.X.hom`, the existing Mathlib lemma
`isAffine_of_isAffineHom G.X.hom` supplies `IsAffine G.X.left`, since the base is
a spectrum. This module adds no separate affineness criterion.

This argument generalizes the field-only
`Langlands.GroupScheme.finiteType_coordinateAlgebra` in
`Rational.SplitComponentProof` to an arbitrary commutative base ring, with
imports confined to the affine-coordinate construction and finite-type
morphisms. It also follows the finite-type transport argument for the distinct
chosen coordinate presentation in `Lie.GroupAlgebraCoordinates`. Both existing
results remain unchanged; the chosen coordinate algebra here is exactly
`AffineCoordinates.algebra`, not the Lie presentation.

The provenance is an internal derivation from these published interfaces and
Mathlib's finite-type spectrum criterion. This helper supplies a prerequisite
for the dominant-combination argument. It does not establish that argument or
the unconditional simultaneous dynamic Levi realization theorem.
