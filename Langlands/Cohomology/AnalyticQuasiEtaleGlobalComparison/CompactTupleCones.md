# Compact lifted tuple cones for compatible quasi-étale covers

`CompactCompatibleTupleConesStatement ρ` is an unproved geometric existence
target for the compact quasi-étale comparison. It works over an arbitrary
complete ultrametric normed field `K : Type u`, an analytic space in
`LocalizedCategory.{u,v,v}`, and a group `G : Type z` with a topology.

For every `CompactLiftBasis ρ` object `i`, every actual
`CompactCompatibleCover ρ i`, every natural number `n`, and every tuple
`α : Fin (n + 1) → Fin c.cover.size`, the proposition asks for an actual wide
pullback cone of the selected covering arrows in `QuasiEtaleSite X`. The cone
must satisfy its categorical universal property against every object of that
site. Its point must be compact and Hausdorff, as encoded by `IsCompactSpace`,
and its structure map to `X` must admit an `ActionLift ρ`. The latter already
includes an open acting subgroup, Berkovich continuity, and structure-map
equivariance.

Tuples may repeat indices, and their length is positive. No empty tuple
product is requested. If the cover has no indices there are no such tuples.
The required lift may use any open subgroup; agreement with the cover's
chosen source actions is not an extra clause of this proposition. The
proposition asserts neither general quasi-étale base-change stability nor
pullbacks in the entire analytic category.

The target has internal provenance. It isolates the geometric input of the
existing `compactCompatibleCechSystem` and
`FiniteBasisCover.cechPresentationOfCones` constructions; it is not a
transcription of a separate assertion in the original literature. No proof
of this existence target is supplied here. In particular, the finite
equivariant refinement hypothesis does not establish these cone and lift
existence clauses. The proposition has no coefficient-ring, sheafification,
topological-group or finite-equivariant-refinement hypotheses. Its proof
remains a separate prerequisite for the global comparison.
