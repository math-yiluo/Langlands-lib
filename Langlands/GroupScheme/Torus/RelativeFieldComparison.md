# Comparing relative tori and field tori

`RelativeFieldTorusComparisonStatement` says that, over every field `k`,
`RelativeTorus.IsTorus G` is equivalent to the field predicate `IsTorus G`.
It is an internal comparison between the two existing definitions, and
`relativeFieldTorusComparison` proves it without additional assumptions.

For a relative torus, choose a point on a member of its étale splitting cover
above the unique point of `Spec k`. The residue field of that point is an
extension of `k`. Pulling the split torus back to that residue field gives a
splitting field for `G`. The proof uses the actual composite of scheme maps
and the base-change composition isomorphism; no rational point on the cover
or separability assertion about this chosen extension is required.

Conversely, the published finite Galois splitting theorem supplies a finite
separable splitting extension of a field torus. Its spectrum is a surjective
étale morphism to `Spec k`, so its single member gives the required étale
splitting cover. This direction uses the proved theorem
`torusFiniteGaloisSplitting`, rather than assuming that the original splitting
extension in the field predicate is separable or finite.

Both predicates concern the actual group scheme and actual group-scheme
isomorphisms. The comparison imposes neither a chosen commutative presentation
nor a chosen rank or global splitting over `k`.
