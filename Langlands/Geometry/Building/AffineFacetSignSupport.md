# Nonnegative root support and the original affine facet order

Let `A` be an affine torsor over a real vector space `V`, in independent
universes, and let `Ψ` be a set of real affine functionals on `A`. This module
derives support comparisons directly from the sign definitions in
`AffineRootSystem` and the original face comparison in
`AffineIncidentFacetLocalization`. It is an internal elementary consequence
of those definitions and results, with no additional literature assertion.

`nonnegativeRootsAt Ψ x` is the set of members of `Ψ` nonnegative at `x`.
`nonnegativeRoots Ψ F` is the set of members of `Ψ` nonnegative at every point
of the supplied subset `F`. These are sets of actual affine functionals.

For `Φ ⊆ Ψ`, `nonnegativeRoots_subset_facet` identifies the `Φ`-support of
`facet Ψ x` with `nonnegativeRootsAt Φ x`: roots of `Φ` have constant signs
on that facet. The special case `nonnegativeRoots_facet` uses `Φ = Ψ`.
`nonnegativeRoots_facetClosure` gives the same support on the existing
combinatorial closure. A closure point either has zero root value or the
same root sign as the representative; the representative itself belongs
to the closure. These three results require no negation stability.

The remaining comparisons assume explicitly

```text
for every ψ ∈ Ψ, -ψ ∈ Ψ.
```

`mem_facetClosure_iff_nonnegativeRootsAt_subset` states

```text
x ∈ facetClosure Ψ y
  ↔ nonnegativeRootsAt Ψ y ⊆ nonnegativeRootsAt Ψ x.
```

For the forward implication, the defining sign alternatives for closure
preserve nonnegativity. Conversely, if `ψ x < 0`, support containment
forces `ψ y < 0`. If `ψ x > 0`, apply support containment to `-ψ` to
force `ψ y > 0`. When `ψ x = 0`, the zero-sign alternative holds.
Thus the original closure condition follows for every root.

`facetClosure_eq_nonnegative_intersection` rewrites this as the intersection
of the nonnegative half-spaces for the roots supported at `y`.
`nonnegativeRootsAt_eq_iff` detects the original point facet relation:
support equality gives both closure inclusions, and the existing closure
equality criterion gives `facetRel Ψ x y`. This is not a newly defined facet
relation.

For actual facets `F` and `G`, the resulting comparisons are

```text
nonnegativeRoots Ψ F = nonnegativeRoots Ψ G ↔ F = G

IsFaceOf Ψ F G
  ↔ nonnegativeRoots Ψ G ⊆ nonnegativeRoots Ψ F.
```

They are `nonnegativeRoots_eq_iff` and
`isFaceOf_iff_nonnegativeRoots_subset`. The proofs choose representatives
of the existing facets and apply the point comparisons.
`facetNonnegativeRootsOrderEmbedding` packages them as an embedding into
the order dual of root subsets, whose order is reverse inclusion. Its
domain relation is explicitly the existing `IsFaceOf`, rather than the
subset order on facet sets. No order is defined by transport.

Fix now `x : A`. `IncidentAffineFacet Ψ x`, from the imported localization
module, consists of full facets whose closures contain the facet of `x`.
`nonnegativeRoots_incidentFacetLocalization` proves that localizing such
a full facet leaves its support for `vanishingRoots Ψ x` unchanged.
Indeed, any full-facet representative computes both supports. Negation
stability of `Ψ` implies negation stability of the roots vanishing at `x`.
Applying the preceding face comparison to the localized facets, then the
imported preservation and reflection of the original face relation, proves
`isFaceOf_iff_incident_nonnegativeRoots_subset`.

`incidentNonnegativeRootsOrderEmbedding` therefore sends an incident full
facet `F` to the roots vanishing at `x` and nonnegative everywhere on `F`.
Its source relation is again explicitly the original `IsFaceOf Ψ`.
Injectivity uses the support embedding for localized facets and the
injectivity of `incidentFacetLocalization`. No finiteness assumption is
needed for this embedding.
`IsAffineRootSystemWithRankZero.incidentNonnegativeRootsOrderEmbedding`
supplies negation stability from the corrected affine root-system axioms,
including the empty rank-zero case. The two general embedding application
lemmas record their forward maps explicitly.

This module proves support detection and reversal of incidence. It does
not classify all parabolic subsets of a finite root system, identify these
affine functionals with special-fibre group roots, or identify actual
facet-model images with parabolic subgroup schemes. The special-fibre
parabolic bijection and the exact unramified facet-model theorem remain
separate obligations.
