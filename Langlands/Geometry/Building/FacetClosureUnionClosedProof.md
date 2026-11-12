# Proof of `FacetClosureUnionClosedStatement`

This module proves
`Langlands.Geometry.Building.FacetClosureUnionClosedStatement` at every
universe `u`:

```
theorem Langlands.Geometry.Building.facetClosureUnionClosed :
    FacetClosureUnionClosedStatement.{u}
```

Take supplied valuation building data `B` over a nonarchimedean local field.
Equip the existing quotient with a metric for which `G(F)` acts by isometries,
and assume that any two points share an apartment, that
`SatisfiesApartmentAxioms` (V 7 and AS 2–AS 5 beyond the data) holds, and
that the apartment map is an isometry for the Euclidean root metric.
Then, for every set `X` of facets of `B(G)`, the union of their topological
closures is closed. This is the second assertion of Kaletha–Prasad Theorem
4.2.10. The set `X` may be infinite, and no local finiteness of the
building is assumed. This proof retains exactly the premises of the published
statement; it constructs neither valuation building data nor a metric or
witnesses to those premises for general groups.

## Declarations

| Lean name | Content |
| --- | --- |
| `AffineRootSystem.facetClosure_subset_closure_facet` | In a real normed affine space, the combinatorial closed facet `facetClosure Ψ p` is contained in the topological closure of `facet Ψ p`, for any set `Ψ` of affine functions |
| `ValuationBuildingData.exists_forall_isFacet_mem_closure` | Under the three premises, every point `x` of `B(G)` has an `ε > 0` such that each facet containing a point at distance `< ε` from `x` has `x` in its closure |
| `facetClosureUnionClosed` | The statement |

The second declaration is the first part of KP Lemma 4.2.11. The Euclidean
root metric of `ValuationApartmentMetric` is installed by local instances, as
in the statement module.

## Sources and provenance

The source assertion and local incidence lemma are in Tasho Kaletha and
Gopal Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 4.2.10
and Lemma 4.2.11, printed pp.171–172 / PDF pp.202–203. Registered source:
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' *Corrections and additions*, version of 1 November 2024,
PDF pp.28–29, add Axiom 4.1.6 to Section 4.2 and make the metric of
Proposition 4.2.1 `G`-invariant. Registered source:
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The statement module's Markdown explains its derived scope: supplied
valuation building data over nonarchimedean local fields, its Euclidean
root metric normalization, and the retained V 7 premise. The affine helper
below is an internal consequence of the Library's sign definitions of facets
and combinatorial closed facets. It holds for any family of affine functions.
The local incidence lemma is a derived formulation of the first assertion
of KP Lemma 4.2.11 on the existing quotient; the proof route is compared below.

Worker 3557 authored the Lean proof and its initial explanation in this
task's shared draft revision 1. Worker 173 checked the proof against the
current Library and completed the source and scope documentation for submission.

## Implemented proof

**Closed facets.** Let `q ∈ facetClosure Ψ p`. Points of the segment from
`q` to `p` with parameter `t ∈ (0, 1]` lie in `facet Ψ p`. For each `ψ ∈ Ψ`,
`ψ` takes the value `(1 - t) ψ(q) + t ψ(p)` there. If `ψ(q) = 0` this value
has the sign of `ψ(p)`. Otherwise `ψ(q)` and `ψ(p)` have the same sign, and
so does the convex combination. The segment tends to `q` as `t → 0⁺`, so `q`
is in the closure of the facet. No local finiteness is used.

**Lemma 4.2.11, first part.** Write `x = g₀ · apartmentMap b`. Local
finiteness of the affine roots, from `SatisfiesApartmentAxioms` through
`isLocallyFiniteReflectionArrangement.finite_bounded_at`, and the published
`AffineRootSystem.eventually_mem_facetClosure` give `ε > 0` such that
`b ∈ facetClosure Ψ a` whenever `dist a b < ε` in `A(S)`.

Let `Y` be a facet and `y ∈ Y` with `dist y x < ε`. The common-apartment
premise gives `h` with `x = h · apartmentMap a₀` and `y = h · apartmentMap a₁`.
The published `exists_normalizer_smul_eq_of_smul_apartmentMap_eq` gives
`n ∈ N(F)` with `n · a₀ = b`. Put `h' = h n⁻¹`. By
`normalizer_smul_apartmentMap`, `h' · apartmentMap (n · a) = h · apartmentMap a`
for every `a`. Hence `x = h' · apartmentMap b` and
`y = h' · apartmentMap (n · a₁)`. Because the action and the apartment map
are isometries, `dist (n · a₁) b = dist y x < ε`
(`dist_smul_apartmentMap`). So `b ∈ facetClosure Ψ (n · a₁)`.

The set `h' · apartmentMap (facet Ψ (n · a₁))` is a facet of `B(G)`
containing `y`. By the published `IsFacet.eq_of_mem_mem` (which uses
`SatisfiesApartmentAxioms`), it equals `Y`. The map `z ↦ h' · apartmentMap z` is
continuous, since the apartment map is an isometry and the action is
isometric. It therefore sends the closure of `facet Ψ (n · a₁)`, which
contains `b` by the first step, into the closure of `Y`. Hence
`x = h' · apartmentMap b ∈ closure Y`.

**The statement.** Let `M = ⋃ Y ∈ X, closure Y` and let `x` be in the closure
of `M`. Take `ε` from the lemma. Some `z ∈ M` has `dist x z < ε`, and
`z ∈ closure Y` for some `Y ∈ X`. The open ball of radius `ε` about `x`
contains `z`, so it meets `Y` in some point `y`. The lemma gives
`x ∈ closure Y ⊆ M`. Thus `closure M ⊆ M`, so `M` is closed.

## Comparison with the source

KP prove Lemma 4.2.11 by choosing a chamber `C` whose closure contains `x`
and an apartment `A` containing it. For a facet `F` meeting the ball they
take an apartment containing `C` and `F` (Proposition 1.5.14) and an element
of `G(k)^0` fixing the closure of `C` and moving that apartment to `A`
(Proposition 1.5.13). The Lean proof instead uses the common-apartment
premise for `x` and one point of the facet. It then moves that apartment
chart by a normalizer element so that `x` has the fixed coordinate `b`, and
identifies the facet through the uniqueness of the facet containing a point.
The radius comes from local finiteness of the affine roots at `b`, instead of
from the minimum distance between parallel hyperplanes. The final closure
argument is a direct topological form of the source's last use of
Lemma 4.2.11. KP additionally prove completeness; here that first assertion
is already available as
`ValuationBuildingData.completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms`.
