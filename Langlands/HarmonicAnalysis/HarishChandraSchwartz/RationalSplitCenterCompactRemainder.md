# A compact central remainder for the actual split-central quotient

This internal auxiliary construction for Task 7500 converts full-central
factors in a supplied group cover into a single compact right factor on the
actual quotient by the split component. It reuses the Library's proved
compactness of the full scheme-center rational-point quotient and its
comparison with the abstract rational-point center.

The generic theorem `Langlands.exists_isCompact_quotient_representatives`
concerns a locally compact topological group `H` and any subgroup `A`. If the
standard coset space `H ⧸ A` is compact, there is a compact subset `C` of `H`
such that every `h` is `c * a` for some `c ∈ C` and `a ∈ A`.
Choose a compact neighborhood `D` of the identity. The quotient map is open,
so the images of all translates of
`interior D` form an open cover of the compact coset space. A finite subcover
provides finitely many translates of `D`; their union is the desired compact
set. Equality of cosets gives the final subgroup factor.

`RationalSplitCenterCompactRemainder s` states that some compact subset `C`
of the abstract center of `G(F)` satisfies

`∀ z ∈ center(G(F)), ∃ c ∈ C, ∃ a ∈ (rationalPoints.map s).range, z = c * a`.

`exists_isCompact_rationalSplitCenter_remainder` proves it over any
nonarchimedean local field in arbitrary universe `u`, for an affine locally
finite type connected reductive group scheme `G` and any actual split
component `s : T.toGrp ⟶ G`.
The published `rationalCenterComparison` identifies full scheme-center points
with the abstract center. The abstract center is closed because it is the
intersection of the closed equalizer sets for commutation with each group
element. Its inherited topology is therefore locally compact. The published
`centerSplitComponentCompactness` gives compactness of the canonical quotient
of these same scheme-center points by `centralRationalPointImage s`. This is
the actual image on rational points, as checked by
`mem_centralRationalPointImage`. Apply the generic compact-representative
theorem and map its compact set into the actual ambient group by subtype
inclusion. These steps use the inherited point topology and the original
split-component image, including for nonsplit groups and trivial split components.

`exists_rationalSplitCentralQuotient_cover_of_central_cover` takes any supplied
cover of `G(F)` of the form

`g = k * a(j) * y * z`, with `k ∈ K`, `y ∈ R`, `z ∈ center(G(F))`,

where `R` is compact, `K` is any fixed subset and `j` ranges over an arbitrary
index type in universe `v`. It proves that there is a compact `Y` such that
the actual left quotient is covered by the sets

`leftQuotientMap (rationalPoints.map s).range '' (K * {a(j)} * Y)`.

Take `Y = R * C` for the preceding compact central remainder. Write the final
central element as `c * b`, with `b` in the actual split-component image.
Centrality moves `b` to the left, where the canonical left-coset map removes
it. The resulting cells use the original index map `a` and left factor `K`
with the new compact right factor.
