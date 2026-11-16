# Finite analytic refinements over one open subgroup

This is an internal construction from the published twisted-category, action-lift
and finite-refinement interfaces. It strengthens the packaging of finite
refinements by producing plain arrows and one common open subgroup. It assumes
the finite equivariant refinement hypothesis; it does not prove that geometric
hypothesis, injective acyclicity, or the global comparison theorem.

The analytic part works over a complete ultrametric normed field, for an analytic
space `X`, a topological group `G`, an action `ρ : G →* Aut X`, and an
isomorphism-invariant morphism property `P`. No continuity of the action on `X`
and no compactness of `X` are required. The admissibility predicate `Adm` on
objects over `X` must be invariant under translation. The plain topology `J`
must be translation invariant, and `liftSystem P ρ Adm` must have finite
equivariant refinements for `twistedTopology ρ J`.

## Intertwining helpers

For an arbitrary category and group with a topology,
`TwistedOver.exists_openSubgroup_intertwines_of_isLocallyEquivariant` concerns an
arrow of twist one between two local actions that are lifts. It applies local
equivariance to the whole source acting subgroup. Comparing twists in the
intertwining equality identifies the source group element with the target group
element. Intersecting the resulting target subgroup with the source subgroup
gives a common open subgroup where the arrow intertwines the same group elements.

The analytic helper `exists_openSubgroup_intertwines_untwist` starts with an
arbitrary twisted arrow `f`, a target local action that is a lift, and a source
action obtained by restricting an actual `ActionLift m`. Write `t` for the twist
of `f`. Local equivariance provides an open subgroup `M` of the target acting
subgroup. Comparing twists identifies each witnessing source element as
`t⁻¹ * g * t`. This proves that `M` lies in the subgroup of `m.translate t`.
The equality of underlying arrows, together with the formula for the translated
action, then proves ordinary intertwining along `untwist t f rfl` on `M`.
The source uses inverse elements because `liftAction` acts by the twisted
endomorphism with twist `g⁻¹`.

## The refinement data and construction

`CommonSubgroupRefinement Adm J a S` is data for one target action `a` of an open
subgroup `Q` and one plain sieve `S` on its object. It contains a natural-number
size, a `Fin size` family of plain source objects and arrows, an open subgroup
contained in `Q`, actual source action lifts whose subgroups contain that common
subgroup, and proofs of source admissibility, membership in `S`, and covering
for `J`. Its `equivariant` field states that every plain arrow, included in the
twisted category, intertwines the same group element for the source lift and the
target action on the common subgroup.

`nonempty_commonSubgroupRefinement` constructs these data. It pushes the plain
covering sieve forward along the inclusion into the twisted category. Its
pullback contains the original sieve, so it is covering. The assumed finite
refinement property gives finitely many twisted arrows with admissible source
actions. Each source is translated by its arrow's twist and its lift is translated
by the same element. The analytic helper supplies an intertwining open subgroup
for each arrow. Intersecting these finitely many subgroups with `Q` gives the
single common subgroup, including when the family is empty. Translation
invariance preserves `Adm`; the published `untwist_mem_of_functorPushforward`
and `covering_untwist_family` give sieve membership and covering for the plain
arrows. `commonSubgroupRefinement` chooses data from this proved nonempty type.

For compact quasi-étale objects the intended specialization is
`P = quasiEtale`, `Adm V = IsCompactSpace V.left`, and `J = quasiEtaleTopology X`.
Translation preserves `V.left` by definition, so admissibility invariance is
immediate. This specialization retains the full-group finite-refinement
hypothesis and does not supply any unproved action-lift existence or compatibility
statement.
