# Balanced-quotient induction on jointly point-continuous atlas actions

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

Let `K : Type u` be a complete normed ultrametric field, `G : Type z`
a topological group, and `H` an open subgroup. Source and target categories
are `PointContinuousNonemptyAtlasAction K H` and
`PointContinuousNonemptyAtlasAction K G`, with presentation universes
`{u, max z v, max z w}`. Their objects carry actual supplied atlas actions
with nonempty original chart spectra and jointly continuous original point
actions; their arrows retain all chosen bounded equivariant data.

`sourceContinuousSMul` derives `ContinuousSMul H (LocalSpace H X.obj)`
for the exact constructed source action `h • x = (X.obj.ρ h).baseMap x`.
The proof is the explicit joint-continuity condition of `X`, since the
original topology and point action are definitionally those of
`LocalSpace`. This proved lemma is installed only as a local instance in
the module. It is a consequence of the input object's property.

The previously constructed balanced quotient has its product-quotient
topology and actual transported coset-copy atlas. Its chart algebras
are the original nonempty source chart algebras, so
`quotient_hasNonemptyCharts` proves their spectrum condition directly.
The existing `continuous_action` theorem supplies joint continuity of
the actual bounded quotient action. Together these construct
`pointContinuousQuotient`, an object of the target continuous full category.
No quotient atlas, quotient action, or output continuity is assumed.

`pointContinuousQuotientFunctor` sends each original full equivariant
arrow to the constructed `quotientEquivariantMap`. The previously proved
whole-arrow identity and composition laws establish functoriality.
The object and map projection lemmas identify these exact constructions.
On representatives the map is `[g,x] ↦ [g,f(x)]`. It retains the coset
tag and original chosen chart target, and its pullback is exactly the
original bounded pullback at that chart. Thus neither functoriality nor
the arrow formulas discard the algebra data.

`continuousSubtype` bundles the actual subgroup inclusion with its
subtype continuity. `pointContinuousRestriction` restricts continuous
full atlas actions along it. The object formula identifies ordinary
categorical restriction; the final functor equality identifies its
forgetting of point continuity with restriction on the nonempty-chart
action category.

The provenance is internal assembly of the constructed quotient atlas,
bounded action and quotient maps with `PointContinuousAtlasActions`.
The continuity bridge uses only the explicit input condition; quotient
continuity uses the proved actual quotient action. Every output object
is constructed. Arbitrary-index subgroups, overlapping charts and empty
spaces with no charts are allowed. Continuity into an analytic
automorphism topology, refinement localization, analytic sites and
Harris tower specialization remain separate obligations.
