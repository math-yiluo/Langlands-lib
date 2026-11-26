# Relative Hom schemes on arbitrary test schemes

`Langlands.AbelianScheme.PointedLaw.HomScheme P X` supplies a scheme `H` over
`S`, a universal evaluation `P ×ₛ H ⟶ X`, and bijections between maps
`T ⟶ H` over `S` and maps `P ×ₛ T ⟶ X` over `S` for all `T` over `S`.
The morphism `H ⟶ S` is separated and locally of finite presentation. The
bijection specializes the evaluation map along the test point. The lemmas
`HomScheme.eval_comp` and `HomScheme.comp_classify` express its naturality.

`exists_homScheme` constructs this data over `S = Spec R` when `P` and `X`
are flat, locally finitely presented, H-projective schemes over `S`. The
published `exists_closedImmersionBySections_iff_isHProjective` supplies the
invertible projective presentations. H-projectivity also supplies
properness, and hence separatedness.

## Affine classification and gluing

The Lean proof applies
`AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat`
and
`AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point`.
The first theorem gives a classification on spectra and the second constructs
the universal evaluation on the resulting scheme. The proof compares the
evaluation at a point and the affine classification using the given universal
map formula. The affine comparison extends along the canonical isomorphism
from the spectrum of global sections to an affine scheme.

For an arbitrary test scheme, restrict a morphism `P ×ₛ T ⟶ X` to the pullbacks
of the affine charts of `T`. The maps from the charts to `H` agree on overlaps
because they have the same evaluation on an affine cover of each overlap.
Gluing these maps gives the classifying point of `T`. The pullback cover
checks its evaluation, and affine uniqueness on `T` gives uniqueness of the
point.

This is the relative Hom scheme used for the closed equation locus in
Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
Proposition 6.16, printed pp. 126–127 (PDF pp. 139–140). The affine charts
implement the passage from the published affine-test Hom classification to
arbitrary test schemes.
