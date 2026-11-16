# Forgetting the canonical local-field package to a complete DVF (M335.002)

`Langlands.NYLL.LubinTate.standardLocalField_toCompleteDVF` proves the
published target
`Langlands.NYLL.LubinTate.standardLocalField_toCompleteDVFStatement K`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Statements`.
The target unfolds to

```lean
(standardLocalField K).toCompleteDVF =
  Langlands.NYLL.LocalFieldTheory.localCompleteDVF K
```

The theorem retains exactly the source telescope, in source order:

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

The argument `K` is explicit and lies in universe zero. No further
hypothesis or universe parameter is introduced. The equation identifies
the complete-DVF parent of the canonical local-field package with the
published canonical complete DVF on the same field and instances.
The theorem retains the source `@[simp]` attribute.

## Implemented proof

The proof first unfolds only the imported proposition definition
`standardLocalField_toCompleteDVFStatement`. It then closes the equality
by `rfl`: the published definition of `standardLocalField K` assigns its
`toCompleteDVF` field to `LocalFieldTheory.localCompleteDVF K`.
Thus projecting that field reduces to the right-hand side. The proof
requires no helper declarations. The imported target and its definitions
are used unchanged.

## Source and attribution

This is the exact proof adaptation of source unit M335.002,
`LubinTate.standardLocalField_toCompleteDVF`, in Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L48-L54)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The docstring is at lines 48–49, the simp attribute at line 50, the
theorem type at lines 51–53 and the reflexivity proof at line 54.
The source section telescope is at lines 37–38. The file SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata directory
contains no note for these source registrations.

The original copyright, Apache-2.0 release line and author header are
retained verbatim. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.

Worker 773 made these modifications on 16 November 2026:

- extracted only M335.002, retaining its name suffix, docstring,
  `@[simp]` attribute and full source telescope;
- changed the namespace from `LubinTate` to `Langlands.NYLL.LubinTate`;
- replaced the six source imports with the single published target
  module, which already supplies all required definitions and instances;
- wrote the theorem type as the fully applied imported target, and added
  its unfolding before the unchanged reflexivity argument;
- retained the source `noncomputable section`, omitted unused scoped
  and namespace opens, replaced the module documentation, and added the
  modification notice and this paired explanation.
