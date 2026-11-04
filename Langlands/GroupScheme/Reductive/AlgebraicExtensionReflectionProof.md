# Reflection along algebraic field extensions

Author: Worker 1554.

The theorem `Langlands.GroupScheme.algebraicExtensionReflection` proves the
unchanged published proposition
`Langlands.GroupScheme.AlgebraicExtensionReflectionStatement.{u}` at arbitrary
universe `u`. The module also proves its two components separately as
`connectedReductiveAlgebraicExtensionReflection` and
`semisimpleAlgebraicExtensionReflection`.

For fields `k K : Type u`, an `Algebra k K`, an instance of
`Algebra.IsAlgebraic k K`, and any actual group scheme `G` over `Spec k`,
write

```text
b   = Spec.map (CommRingCat.ofHom (algebraMap k K)),
G_K = (GroupScheme.baseChange b).obj G.
```

The two conclusions are `IsConnectedReductive G_K → IsConnectedReductive G`
and `IsSemisimple G_K → IsSemisimple G`, respectively. Each implication has
only the displayed premise on the actual group scheme. In particular, the
extension may be infinite or inseparable, and the fields may be imperfect
and have positive characteristic. The centre in the semisimplicity predicate
is the full scheme-theoretic centre, including its nonreduced structure.

## Implemented proof and provenance

This is an internal specialization of the published module
`Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`.
That module proves `IsConnectedReductive.of_fieldExtension` and
`IsSemisimple.of_fieldExtension` for arbitrary field extensions, with
implicit parameters `k`, `K` and `G`. Their base change and their predicates
are exactly those in the two components of the target.

Each component proof introduces the two fields, their field instances, the
algebra structure, the algebraicity instance, the group scheme and the
displayed premise. It then applies the corresponding field-extension
reflection theorem. The algebraicity instance is unused because the imported
theorems apply to every field extension. The final theorem pairs these two
proofs using the conjunction that defines
`AlgebraicExtensionReflectionStatement`.

The imported connected-reductivity theorem already derives smoothness,
affineness, connectedness and triviality of the geometric unipotent radical.
The imported semisimplicity theorem also derives an actual finite
representative of the full centre over the original field. This module
therefore requires no additional property of `G` and no additional condition
on its algebraic extension. The proof introduces no external assertion or
new axiom. Its provenance is the specialization and conjunction of these
implemented Library results; the original-source provenance of the target
remains in the unchanged statement's paired Markdown.
