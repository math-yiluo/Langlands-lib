# Proof of `BoundedSubgroupFixedPointStatement`

This module proves
`Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement` at every
universe `u`:

```
theorem Langlands.Geometry.Building.boundedSubgroupFixedPoint :
    BoundedSubgroupFixedPointStatement.{u}
```

For supplied data satisfying the five axioms of the corrected opening of
Kaletha–Prasad Section 4.2, an algebraically bounded subgroup `H` of `G(F)`
fixes a point of the existing quotient. For every metric realization of that
quotient, `H` also fixes a point of each nonempty closed convex subset that
it preserves.

## Lemmas for one metric realization

The lemmas are in the namespace
`Langlands.Geometry.Building.ValuationBuildingData.MetricRealization`. They
take a supplied `B : ValuationBuildingData G` over a nonarchimedean local
field and `M : B.MetricRealization`, with the metric `M.metric` installed on
`B.ReducedBuilding`.

| Lean name | Content |
| --- | --- |
| `isBounded_image_smul` | If `S ⊆ G(F)` is algebraically bounded, then `{g • y : g ∈ S}` is bounded for every point `y` |
| `exists_fixed` | An algebraically bounded subgroup `H` has a point `x` with `h • x = x` for all `h ∈ H` |
| `exists_fixed_mem` | Such `H` fixes a point of every closed, geodesically convex, `H`-stable `Y` |

`smulIsometry`, `image_orbit_eq` and `image_eq_of_forall_mem` are private
helpers.

## Proofs as implemented

*Bounded orbits.* `isBounded_image_smul` installs the canonical topology
`rationalPointTopology F G.X` on `rationalPoints G`. Smoothness from
`B.isConnectedReductive` gives local finite type, so the published
`IsAlgebraicallyBounded.isCompact_closure` makes the closure of `S` compact.
The orbit map `g ↦ g • y` is continuous by the field `M.continuous_orbit`.
So the image of the closure is compact, hence bounded, and it contains the
image of `S`.

*A fixed point.* `exists_fixed` uses completeness (`M.complete`) and the NPC
property (`M.nonpositivelyCurved`). The published `completeNPCGeodesic`
then makes the quotient a geodesic space. Choose a point `y₀` of the nonempty
apartment and let `O` be the orbit `H • [y₀]`. It is nonempty, and bounded
by the previous lemma. The published `boundedSetStabilizerFixedPoint`
(KP Theorem 1.1.15(2)) gives a point `b` fixed by every isometry equivalence
`e` with `e '' O = O`. For `h ∈ H` the action of `h`, packaged by the
private `smulIsometry` as `IsometryEquiv.constSMul h` (using `M.isometric`),
carries `O` onto itself, because `h H = H` (`image_orbit_eq`). Hence
`h • b = b`.

*A fixed point in `Y`.* `exists_fixed_mem` applies the published
`nearestPointProjection` (KP Proposition 1.1.20) to the closed convex set `Y`.
It obtains a projection `π` onto `Y` that commutes with every isometry
equivalence carrying `Y` onto itself. For `h ∈ H`, stability of `Y` under
`h` and `h⁻¹` gives `h '' Y = Y` (`image_eq_of_forall_mem`). With `b` from
`exists_fixed`, equivariance gives `π (h • b) = h • π b`, and `h • b = b`
gives `h • π b = π b`. The point is `π b ∈ Y`.

## The statement

`boundedSubgroupFixedPoint` introduces the data and the seven premises, with
the instance `IsAffineHom G.X.hom` taken from `hG`. The published
`metricRealization` applied to the same premises gives some
`M : P.toValuationBuildingData.MetricRealization`. The first conjunct is
`M.exists_fixed`. The second conjunct, for an arbitrary realization `M'`,
is `M'.exists_fixed_mem`.

The route differs from the source proof of KP Corollary 4.2.14, which
relates algebraic boundedness to bounded orbits through Proposition 4.2.13.
Here that link is the compactness of the closure in the local-field topology
together with continuity of orbit maps. All seven premises are consumed
only by `metricRealization`. The second clause uses the projection of
Proposition 1.1.20 rather than a fixed-point argument inside `Y`.

All declarations use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence and scope

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Corollary 4.2.14, printed p.173 / PDF p.204. Both its ambient fixed-point
conclusion and its conclusion for a preserved nonempty closed convex subset
are proved here. The subset may be unbounded.

The registered corrections `kaletha-prasad-2024-corrections`, version of
1 November 2024, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.1–2 and 28–29, require nonempty convex sets, add Axiom 4.1.6 to
Section 4.2, and require the constructed metric to be invariant. The exact
published target retains these conventions through its seven supplied-data
premises and `MetricRealization`. These original pages were compared with
the target and this proof explanation in preparing this proof unit.

The formal scope is the derived local-field specialization explained in
[the statement](BoundedSubgroupFixedPointStatement.md): every
nonarchimedean local field of either characteristic and every connected
reductive group scheme at universe `u`, on the supplied actual quotient.
The second conclusion holds for every `MetricRealization` of that quotient.
The proof adds no bounded-orbit, fixed-point, metric-existence or
data-existence hypothesis, and does not assume Proposition 4.2.13. It does
not construct the supplied `ParahoricBuildingData` or its axiom witnesses;
their construction remains the separate
`RootValuationBuildingConstructionStatement`.

## Authorship and verification

The Lean proof and its initial explanation are Worker 3557's shared Task 5270
draft, revision 1. Worker 123 checked it against the published interfaces and
the cited original pages and completed this source and scope explanation.
The Lean implementation is unchanged from that draft.

Development check `ccb8a085-e68a-4aea-a9de-881e7f850a23`, in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, compiled the module with no
errors or warnings and inspected `boundedSubgroupFixedPoint` as a theorem
with sole universe parameter `u` and axiom set `propext`, `Classical.choice`,
`Quot.sound`. This development check is separate from exact-target
validation, independent semantic review and publication.
