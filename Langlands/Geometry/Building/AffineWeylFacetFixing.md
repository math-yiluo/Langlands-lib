# Pointwise fixing of facets by affine Weyl elements

`Langlands.Geometry.Building.AffineRootSystem.pointFixingChamberTransport`
constructs a chosen affine Weyl element carrying one regular point into the
chamber of another, when their chamber closures contain a common point.
The constructed element fixes that common point. Its arguments include the
arrangement, both regularity proofs, and both closure-incidence proofs.
The construction uses classical choice from the proved
`exists_facetRel_fixing`; it imposes no uniqueness or canonicity claim.
`pointFixingChamberTransport_apply` and
`pointFixingChamberTransport_facetRel` give its two defining properties.

The resulting `affineWeyl_facet_fixing` says
that every element of the existing `affineWeylGroup Ψ` whose affine image
preserves a full facet as a set fixes every point of that facet. It assumes
the five fields of `IsLocallyFiniteReflectionArrangement Ψ`, on a real vector
space and affine torsor in independent universes `uV, uA`. Nonreduced
arrangements and rank zero are included. This internal geometric unit does not
assert a comparison between an actual simply connected normalizer action and
the affine Weyl group.

`IsLocallyFiniteReflectionArrangement.exists_regularPoint_closure` first
places every point in the closure of a regular facet, by
choosing a direction nonzero under every derivative root and moving a small
positive distance along it. Local finiteness preserves all initially nonzero
signs. `mem_facetClosure_apply_iff` transports the defining weak sign
conditions by precomposing the roots with a root-preserving affine map and
its inverse. `root_eq_zero_of_mem_closures` proves that a root separating two
points vanishes at any common point of their facet closures: otherwise the
two root signs would agree.

`exists_facetRel_fixing` proves that two chambers incident to a point can be
transported by an affine Weyl element fixing that point. Strong induction on
the number of separating roots uses the published `exists_wall` lemma to
choose a separating wall. The preceding vanishing result makes its reflection
fix the common point. Closure transport preserves incidence, and the published
`separatingRoots_ssubset` strictly decreases the finite set of separating
roots. Compose the recursively obtained transport with this reflection.
When there are no separating roots, the two regular points already have the
same sign for every root, so the identity suffices.

`eq_of_facetRel_apply` proves the stronger assertion that an affine Weyl
element carrying a point into the same facet fixes that point. A regular
chamber incident to the point and its image are both incident to that point.
The defined `pointFixingChamberTransport` carries the chosen chamber to the same
chamber as the given element. Their quotient therefore stabilizes the chosen
chamber. The published wall-generation theorem and
`chamber_stabilizer_eq_one`, supplied with the proved
`reflectionGalleryFreeness`, make this quotient the identity. Thus the given
element equals the local transport and fixes the point.
Finally, `affineWeyl_facet_fixing` uses membership of a point and its image in
the same full facet to apply this assertion.

The argument is derived internally from the published
`AffineReflectionGalleryGeometry`, `AffineChamberFreeness` and
`ReflectionGalleryFreeness` modules. The generic-direction construction extends
`IsLocallyFiniteReflectionArrangement.exists_regularPoint` in
`FacetFixingWeylReduction`; the quotient computation follows the published
`AffineChamberTransitivity` proof. The module introduces no new proposition
target or external source claim. No external Lean code is used. Worker 1617
authored this extension from the published results.
