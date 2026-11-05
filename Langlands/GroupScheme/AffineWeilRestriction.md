# Actual affine group-scheme Weil restriction

Worker 1642 constructs `Langlands.GroupScheme.AffineWeil.groupScheme A B G`,
an actual group object in `Over (Spec (CommRingCat.of A))`. The commutative
rings `A` and `B` inhabit one arbitrary universe `u`. The hypotheses are
`Algebra A B`, `Module.Finite A B`, `Module.Projective A B`, an actual group
scheme `G` over `Spec B`, `IsAffine G.X.left`, and
`LocallyOfFiniteType G.X.hom`. There is no group commutativity, smoothness,
reductivity, splitness, Noetherianity, or finite-presentation assumption.

## Internal provenance and construction

This is an internal derivation from the published modules
`Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestriction`,
`Langlands.RingTheory.WeilRestriction.FiniteType`,
`Langlands.GroupScheme.AffinePoints`, and
`Langlands.GroupScheme.Corepresented`. It uses these constructions by Lean name;
it copies no outside code and invokes no further structural assertion. The
paired Markdown of those modules records their original source provenance.
This adapter supplies algebraic infrastructure for the Getz–Hahn (2.20)
consumer; it does not prove that source's rational split-centre comparison.

`tensorFunctor A B` sends an actual commutative `A`-algebra `T` to
`B ⊗[A] T`, and an algebra map to `Algebra.TensorProduct.lTensor B` of
that map. `pointFunctor A B G` composes it with the original group's
`affinePointFunctor`. Consequently its values have the actual point-group
laws induced by `G`'s multiplication, unit, and inverse morphisms.

`coordinateAlgebra A B G` is exactly
`WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)`, bundled as
an `A`-algebra. The imported finite-type bridge supplies finite type of the
original affine group's global-section algebra from the stated local-finite-type
hypothesis. `classifyingEquiv` applies the algebra's published `homEquiv`
and then the inverse of `affineSchemePointEquiv` to obtain actual points of
`G`. `classifyingEquiv_coordinates` identifies this map with `homEquiv`
in the original group's global-section coordinates.

`coordinatePoint_changeRing` proves that the coordinate classification
respects coefficient algebra maps. Its proof computes the inverse image under
`Spec` of the composite of the coefficient spectrum map, the actual point,
and the canonical affine presentation. Contravariance and full faithfulness of
`Spec` give exactly postcomposition of algebra maps.
`corepresentableBy` combines this identity with `homEquiv_comp` to verify
naturality of `classifyingEquiv`.

`Corepresented.groupScheme` transfers the actual group-valued functor to a
cogroup structure on this representing algebra and applies relative spectrum.
Thus `groupScheme` includes actual multiplication, unit and inverse morphisms
with their laws, rather than only a group structure on a selected point set.
`groupScheme_X` proves that its underlying relative scheme is definitionally
`affineWeilRestriction A B G.X`. The module supplies affineness and local
finite type as instances by reusing the corresponding published scheme instances.

## Canonical multiplicative points

For every commutative `A`-algebra `T` in `u`, `pointsEquiv A B G T` is a
multiplicative equivalence from this actual group's affine `T`-points to the
original group's actual affine `(B ⊗[A] T)`-points. It is the published
`Corepresented.affinePointsEquiv` for the preceding corepresentation, so it
preserves multiplication, identity and inverse using the original group-object
laws. No comparison or group-compatibility premise is added.

`pointsEquiv_eq` proves that its underlying equivalence is exactly
`affineWeilRestrictionPointEquiv A B G.X T`.
`spectrumPoint_preimage` identifies the algebra map recovered by the fully
faithful relative spectrum functor with `affineRingPointEquiv`; substitution
into `classifyingEquiv` proves the equality.
`pointsEquiv_coordinates` records the resulting explicit equation: the
original group's global-section coordinate map of the image point is
`WeilRestrictionFiniteType.homEquiv` applied to the restricted point's
`affineRingPointEquiv`. `pointsEquiv_naturality` proves that changing
coefficients by `a : T →ₐ[A] T'` acts on the target by the actual
point pullback of `id_B ⊗ a`.

This module asserts no full restriction-of-scalars adjunction on arbitrary
test schemes, preservation of reductivity or smoothness, split-centre
comparison, adelic tensor decomposition, or measure comparison. Induced group
homomorphisms, the commutative variant, and the topological base-point comparison
are supplied by separate adapter modules.
