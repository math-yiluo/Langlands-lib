# Exhaustion of the all-compact constituent part

Author: Worker 88. This internal helper supports the converse of Renard IV.1.7,
Proposition (printed pp.95–96 / PDF pp.101–102), using the projectivity result
of IV.1.6 (printed pp.94–95 / PDF pp.100–101). The original is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
This is a derived proof step, not an additional hypothesis of the final theorem.

`totalIsotypic_eq_top_of_compact_irreducible_subquotients` takes a smooth complex
object `A` of a Hausdorff locally compact totally disconnected group. Its only
representation-theoretic premise is that every actual irreducible subquotient
of `A` has compact smooth-dual coefficients. The group universe and carrier
universe are independent. It concludes that the published total intrinsic
compact-isotypic subrepresentation `T` is top. Neither (KF), finite type,
countability, a measure, nor a chain condition is assumed.

If `T` is proper, choose a vector outside it. Its image in the actual quotient
`Q = A/T` is nonzero, so the published irreducible-subquotient existence theorem
gives `D` as an actual irreducible subquotient of `Q`. Subquotient transitivity
also makes it a subquotient of `A`, and the premise therefore makes `D` compact.
The published `CompactCoefficient.projective_of_hasCompactSmoothDualCoefficients`
provides projectivity of `D` in the same smooth category.

Present the occurrence in `Q` by `i : C → Q` injective and `q : C → D`
surjective. Projectivity supplies `s : D → C` with `q ∘ s = id`. Thus
`f = i ∘ s : D → Q` is injective. Apply projectivity again to lift `f`
along the actual quotient map `A → Q`, obtaining `t : D → A` whose composite
is `f`. Bundle `D` as an irreducible compact-coefficient representative.
The defining range containment for its isotypic class puts the whole image
of `t` in `T`. Hence the composite with `A → Q` is zero. Applying this to
a nonzero vector of `D` contradicts injectivity of `f`.

`compactCoefficients_of_compact_irreducible_subquotients` then observes that
every vector of `A` lies in its total isotypic part. The published
`totalIsotypicSubrepresentation_le_compactCoefficientVectors` gives compact
ambient smooth-dual coefficients for each such vector, proving compactness
of `A` itself. This consequence is included for reuse; the splitting converse
uses the preceding exact exhaustion equality.

All quotient maps, injections, surjections and lift equations are actual
Library `SmoothRep` maps. The implementation uses no quotient category or
abstract constituent placeholder. It is an internal consequence of published
projectivity, actual subquotient transitivity, irreducible-subquotient existence
and the definitions of intrinsic isotypic parts.
