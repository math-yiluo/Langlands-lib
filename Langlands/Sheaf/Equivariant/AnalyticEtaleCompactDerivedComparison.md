# Compact étale comparison from restricted-injective acyclicity

This is an internal conditional construction. It specializes the generic exact
derived base-change criterion to the actual analytic compact-support comparison.
It leaves two mathematical premises explicit and does not prove the full
`AnalyticEtaleCompactComparisonStatement`.

The parameters are a complete ultrametric normed field `K`, a normed extension
field `L`, an analytic space `X`, the point axioms `h` for its `L`-valued points,
a topological group `G` acting by analytic automorphisms through `ρ`, and a
commutative ring `R` in universe `max u (v + 1) uL`. The group is small in that
universe, and the distinguished lift system has admissible refinements on the
twisted étale site. No Hausdorffness, point-projection surjectivity, or continuity
of the action is assumed by this conditional construction; such geometry is
needed to establish its premises in the intended application.

`isIso_etaleCompactComparison_of_injective_acyclic` takes:

- `hzero`, saying that the actual inclusion `etaleCompactInclusion` from smooth
  compactly supported sections to compactly supported sections of the
  restriction is an isomorphism;
- `hacyclic`, saying that for every injective étale `G`-sheaf `I` and every
  natural number `r`, the plain compactly supported cohomology of `b^* I`
  in degree `r + 1` is zero.

It proves that the existing `etaleCompactComparison` is an isomorphism in every
natural-number degree. Injectivity belongs to `I` before restriction; the
premise asserts acyclicity of the restricted object.

The proof installs the existing analytic sheafification, enough-injectives and
size instances. The published exactness results supply the finite-limit and
homology preservation needed for `b^*`, while `smoothForget` is exact.
The compact-sections functors are additive and left exact. Unfolding the
comparison identifies it with `ExactBaseChange.baseChangeNatTrans` of
`etaleCompactInclusion`, so
`ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic` applies directly.
The generic criterion uses an injective resolution and its exact image, with
the image terms acyclic by `hacyclic`.

`etaleCompactComparisonIsoOfInjectiveAcyclic` packages that same comparison as a
natural isomorphism. Its `_hom` theorem records that the forward map is exactly
the existing canonical comparison.

This provenance is internal: the result is a specialization of the generic
criterion to the existing analytic functors and exactness theorems. Establishing
either premise from the geometric hypotheses of Berkovich's theorem remains a
separate obligation.
