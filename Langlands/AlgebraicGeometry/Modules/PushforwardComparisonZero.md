# Degree-zero compatibility of the pushforward comparison

This internal helper identifies the published `compComparison` and
`pushforwardComparison` in degree zero with the ordinary functor comparisons.
It uses the actual maps and canonical zeroth-right-derived identifications,
rather than choosing new isomorphisms between their sources and targets.

For additive functors `F : C → D`, `G : D → E`, `H : C → E` between
abelian categories, an isomorphism `e : F ⋙ G ≅ H`, and an object `A`
with vanishing positive right derived functors of the left exact `F`,
`toRightDerivedZero_compComparison` identifies
`H.toRightDerivedZero(A) ≫ compComparison(G,e,A,0)` with
`e.inv(A) ≫ G.toRightDerivedZero(F(A))`. Injective resolutions are
assumed for `C` and `D`; the universe parameters are arbitrary.

The proof uses the same injective resolution as the published comparison.
It compares the degree-zero cycles maps by their inclusions into the
degree-zero terms, using naturality of `e` on the augmentation. Naturality
of the homology projection and the published augmentation comparison
formula then give the equality.

When `G` and `H` also preserve finite limits, `compComparison_zero`
expresses the comparison as `H.rightDerivedZeroIsoSelf.hom`, then
`e.inv`, then `G.rightDerivedZeroIsoSelf.inv`.
All three factors are isomorphisms. The instance
`isIso_compComparison_zero` therefore proves the canonical comparison
invertible in degree zero, and `compComparisonZeroIso` packages that
same forward map as an isomorphism. This needs no assumption that `F`
sends injective objects to `G`-acyclic objects, unlike the
published all-degree invertibility criterion.
For scheme module pushforward, `pushforwardComparison_zero` specializes
this to `relativeGlobalSectionsCompIso`, through
`relativeCohomologyZeroIso` on both sides.

All assertions are internal consequences of the published
`PushforwardComparison`, `CohomologyBaseChange`, and acyclic-resolution
comparison modules, together with pinned Mathlib's `toRightDerivedZero`
and homology naturality. No external mathematical assertion is used.
This helper does not assert a base-change isomorphism or the relative
cube theorem.
