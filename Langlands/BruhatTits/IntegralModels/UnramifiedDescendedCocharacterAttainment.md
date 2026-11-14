# Actual facet models along descended cocharacter rays

This internal supporting result is derived from the published positive-root
reduction criterion, prescribed-ray quotient-image theorem, no-inversions
theorem, exact facet-restriction embedding, and computation of the linear part
of the descended apartment map.

The ground field is an arbitrary nonarchimedean local field at universe `u`.
The downstairs building satisfies its apartment axioms and the common-apartment
condition. Its map to the maximal-unramified building is equivariant, agrees
with a supplied affine apartment map, and exactly restricts affine facets.
The supplied facet-model family is characterized after unramified base change
by the zero-point subgroup intersected with the pointwise fixer of each facet's
image. A homomorphism from the base-changed downstairs apartment torus into
the upstairs torus must factor its generic inclusion.

For a supplied downstairs facet-model family characterized after maximal
unramified base change, every cocharacter of its apartment torus determines a
positive short ray and an actual incident downstairs facet. The quotient image
of the supplied morphism from that facet, after unramified base change, is the
dynamic parabolic of the corresponding specialized upstairs cocharacter.
The equality is of subgroup functors on all scheme tests.

The proof first identifies the zero fixer of the image of a downstairs facet
with that of its image point. Both subsets lie in the same full upstairs facet,
so the published zero-group no-inversions theorem applies. The supplied model
therefore satisfies the singleton characterization required by the ray theorem.
The descended apartment linear-part computation puts the chosen ray in the
image of the downstairs apartment. The full-facet restriction embedding reflects
its incidence. The source model and morphism used in the quotient-image theorem
are the actual ones in the supplied family at this downstairs facet.

`FacetModelData.HasDescendedCocharacterQuotientAttainment` is the Prop-valued
statement, proved by `FacetModelData.hasDescendedCocharacterQuotientAttainment`.
The main explicit theorem is
`FacetModelData.exists_incidentFacet_quotientImage_eq_descendedCocharacter`.
Its chosen facet is the facet at the downstairs point obtained by translating
the base point by the class of `ε ⊗ c` in the apartment translation space,
for some `ε > 0`. The equality uses the reductive image inclusion of the
actual supplied morphism after base change and the given reductive quotient
after base change.

This result concerns cocharacters of the specified downstairs apartment torus
and a supplied generic torus factorization. It does not assert that all
ground-field parabolics have this form, or prove the full host order bijection.
