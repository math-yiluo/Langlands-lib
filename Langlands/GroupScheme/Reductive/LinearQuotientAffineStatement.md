# Affineness of actual linear quotients by connected reductive subgroups

Worker 708.

`Langlands.GroupScheme.ReductiveLinearQuotientAffineStatement` is an internal
proposition at every universe `u`. This file states a missing geometric input;
it supplies no proof of that input.

The proposition quantifies over every algebraically closed field `k : Type u`,
in arbitrary characteristic, and every actual group scheme `G` with the
published predicate `IsConnectedReductive G`. For every natural number `N`
and every representation `ρ : G → GL_(Fin N)` that is a closed subgroup
embedding, it asserts affineness of every supplied actual homogeneous
quotient `Q` of `GL_(Fin N)` by this particular embedded `G`.

Here `Q` has the published type
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ`. In particular,
its relative scheme is separated, locally of finite type and quasi-compact.
Its projection is smooth, surjective and quasi-compact. Its fibers satisfy
the exact right-coset criterion on every relative scheme test:
`g ≫ Q.projection = h ≫ Q.projection` if and only if
`g⁻¹ * h ∈ (SubgroupFunctor.range ρ).carrier T`. The tests may be nonaffine
or nonreduced. The conclusion is `IsAffineHom Q.scheme.hom` for that same
quotient. It does not substitute a different affine model.

The statement adds no geometric-reductivity assumption, characteristic
restriction, or supplied affineness certificate. The existing reductivity
predicate retains its definition through the geometric unipotent radical.
All natural numbers `N`, including zero, are quantified.

## Internal provenance and intended use

This is a purpose-built prerequisite for an affine homogeneous space route
to `DynamicQuotientProperStatement`. Its exact formulation uses the
Library's actual general linear group, representations, closed subgroups
and homogeneous quotient data. It is not presented as a literal
transcription of a passage of the literature.

The converse result `AffineHomogeneousQuotientReductiveStatement` does not
prove this proposition. Nor does the general theorem about affine
*group-scheme* quotients apply to this homogeneous space: the subgroup need
not be normal, and the quotient carries no assumed group law.

The companion module `LinearQuotientAffineReduction` proves that this
proposition, together with the published closed linear embedding and smooth
subgroup quotient existence theorems, supplies an actual closed linear
embedding of each connected reductive group and an affine homogeneous
quotient for it. The construction retains all the quotient data just
described.

For the intended properness application, a proof of this proposition must
be independent of the regular-cocharacter/Borel route and of the excluded
parabolic-dynamic and rank-one inputs of Task 6453. This is a requirement
on a future proof, not an additional logical premise of this proposition.
Publishing the present statement establishes neither its truth nor
properness of a supplied dynamic quotient. The latter still requires the
geometric extension argument and comparison with the supplied `Q,q`.
