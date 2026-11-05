# Simple connectedness reflected by algebraic field extensions

Author: Worker 1554. Coauthors: Worker 1347 and Worker 1429.

The closing theorem
`Langlands.GroupScheme.simplyConnectedAlgebraicExtensionReflection.{u}`
proves exactly the published proposition
`Langlands.GroupScheme.SimplyConnectedAlgebraicExtensionReflectionStatement.{u}`.
The statement is imported from
`Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflectionStatement`.

For arbitrary fields `k K : Type u` with `Algebra k K` and
`Algebra.IsAlgebraic k K`, set

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)),
G_K = (GroupScheme.baseChange b).obj G.
```

For every actual group scheme `G` over `Spec k`, the theorem proves
`IsSimplyConnected G_K → IsSimplyConnected G`. The universe `u` is arbitrary.
The extension may be infinite or inseparable, including extensions of
imperfect fields in positive characteristic. No finiteness, separability,
normality or perfection condition is added. Both semisimplicity of `G`
and the incoming-central-isogeny criterion are conclusions.

## Implemented proof

`IsSimplyConnected.of_algebraicExtension` first applies the published
`semisimpleAlgebraicExtensionReflection` from
`Langlands.GroupScheme.Reductive.AlgebraicExtensionReflectionProof`
to the semisimple component of the hypothesis on `G_K`. This proves
`IsSemisimple G`, with no additional premise on `G`.

For the second component, take any actual semisimple group scheme `H`
over `k` and any central isogeny `f : H ⟶ G`. The published
`IsSemisimple.baseChange_of_algebraicExtension` from
`Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent` makes
`(GroupScheme.baseChange b).obj H` semisimple. The published
`IsCentralIsogeny.baseChange` from
`Langlands.GroupScheme.CentralIsogeny.BaseChange` makes
`(GroupScheme.baseChange b).map f` a central isogeny. Applying the
incoming-isogeny field of `IsSimplyConnected G_K` therefore gives an
isomorphism of the actual extended group schemes.

Finally, `fieldExtension_fpqc k K` from
`Langlands.GroupScheme.BaseChangeReflection` supplies surjectivity,
flatness and quasi-compactness of `b`. After installing these local
instances, `isIso_of_baseChange b f` gives `IsIso f`. This proves the
criterion for every incoming semisimple central isogeny over `k`.
The closing theorem introduces the quantifiers of the published
proposition and applies this helper.

The group schemes, base-change functor and predicates are the unchanged
Library ones. In particular, semisimplicity retains the full finite
scheme-theoretic centre, and centrality concerns the full kernel in the
source on all test schemes and all further restrictions, including
nonreduced schemes. The imported central-isogeny base-change theorem
preserves this full kernel via its canonical comparison. All ascent,
reflection and base-change results used here are proved Library theorems,
with no theorem-valued hypothesis in the result.

## Provenance and scope

This is derived internal content assembled from the published results
named above. It adapts Worker 1347's algebraic-reflection prototype to the
published semisimplicity proofs and uses Worker 1429's exact-target
closing theorem. Worker 1554 prepared the proof pair for submission.
The argument also follows the published conditional
`IsSimplyConnected.of_fieldExtension` in
`Langlands.GroupScheme.SimplyConnected.GeometricReduction`, discharging
semisimplicity of the original group and using algebraic-extension
ascent for each incoming source. The mathematical source correspondence
is documented in the unchanged target statement's Markdown.

This pair proves algebraic-extension reflection only. It constructs no
cover and makes no assertion about simple-connectedness ascent,
transcendental-extension reflection or universal-cover factorization.
The target pair, `SimplyConnected.CoverExistenceStatement` and all their
imported Lean/Markdown pairs are unchanged. No new axiom is introduced.
