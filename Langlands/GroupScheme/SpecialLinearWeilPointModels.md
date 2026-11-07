# Actual tensor point models of restricted special-linear roots

For a finite field extension `E/F`, with both fields in arbitrary universe
`u`, and any finite matrix index type `n : Type`, this internal construction
identifies points of the existing actual restriction `Res(E/F) SLₙ`
on every relative test scheme `T` with determinant-one matrices over
`E ⊗[F] Γ(T, 𝒪_T)`. The algebra structure on the global sections is the actual
relative one supplied by `algΓ`. No affineness condition on `T`, separability
condition on `E/F` or characteristic restriction is imposed.

The helper `SpecialLinear.Root.affinePointsEquiv_rootMap` first identifies
the original actual coordinate-root map over an arbitrary commutative ring
`R` on every affine test algebra `S`. Its matrix is the transvection whose
coefficient is the original affine additive coordinate.
The proof transports the existing global-section root formula along
`Corepresented.affineSectionsIso S`. The forward section comparison recovers
both the original matrix coordinates and the original additive coordinate.
Compatibility of transvections with ring maps gives the result.

For the restriction, `WeilRoot.sectionAlgebra F T` is exactly
`((algΓ (CommRingCat.of F)).obj T).unop`.
The algebra `tensorAlgebra F E T` is its tensor extension by the existing
`AffineWeil.tensorFunctor`. Its underlying ring is the displayed tensor
product.

The equivalence `tensorMatrixEquiv F E T` composes the existing
`Corepresented.pointsEquiv` for the actual restricted group with the original
SLₙ affine matrix comparison on the tensor algebra.
The equivalence `tensorRootCoordinates F E T` similarly identifies points
of the actual restricted additive group with one additive coordinate in
the tensor algebra, represented as `Multiplicative (Fin 1 → tensorAlgebra)`.
These are equivalences of actual point groups.

For an actual relative map `a : T' ⟶ T`, `tensorMap F E a` is the ring map
induced by applying `AffineWeil.tensorFunctor` to the actual relative
global-section pullback. The theorem `tensorMatrixEquiv_naturality` proves
that pulling back an actual restricted SLₙ point applies this ring map
entrywise. The theorem `tensorRootCoordinates_naturality` gives the same
pullback formula for the additive-root scalar. Both use the existing
all-test corepresented comparison followed by its affine naturality.

The theorem `tensorMatrixEquiv_rootMap` computes the actual restricted
root morphism from `SpecialLinearWeilRootGroups` on every test scheme.
Its matrix is the scalar transvection at the specified distinct indices,
with coefficient given by `tensorRootCoordinates`.
The proof applies `Corepresented.groupSchemeMap_points` to the actual
`AffineWeil.map`, then uses the original affine root formula proved above.
Thus the statement concerns the previously constructed restricted morphism,
including nonaffine test schemes.

The provenance is internal composition of the existing actual restriction,
relative-global-section and affine point comparisons. The section-isomorphism
calculation relates the original coordinate-root morphism to its affine
description; all remaining formulas follow from the stated naturality and
actual induced-map formulas. This unit does not yet construct a cocharacter
or contraction of restricted roots, compare parabolic radicals under
restriction, or prove the unrestricted local Kneser–Tits theorem.
