# The finite intrinsic base is the distinguished finite base: proof

This module proves the published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_baseStatement`
(source row M091.007) by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base`.
The theorem's type is exactly that proposition, with no parameters of its own.

Its only import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Statements`,
the published module that contains the statement. That published
Lean/Markdown pair and everything it imports stay unchanged.

## Target

For every field `F : Type`, the statement asserts

```lean
intrinsicFiniteAbstractBase F =
  Langlands.NYLL.ClassFormation.FiniteAbstractField.base
    (intrinsicAbsoluteGalois F)
```

an equality of two terms of
`FiniteAbstractField (intrinsicAbsoluteGalois F)`, where
`intrinsicAbsoluteGalois F` is `Gal(SeparableClosure F / F)`. The left side
has `field := intrinsicAbstractBase F`, the closed fixing subgroup of the
bottom intermediate field; the right side has
`field := baseField (intrinsicAbsoluteGalois F)`, the closed subgroup `⊤`.

## Implemented proof

```lean
  intro F _
  have h := closedFixingSubgroup_bot_eq_baseField F (SeparableClosure F)
  change intrinsicAbstractBase F =
    baseField (intrinsicAbsoluteGalois F) at h
  have key : ∀ K L : FiniteAbstractField (intrinsicAbsoluteGalois F),
      K.field = L.field → K = L := by
    rintro ⟨_, _⟩ ⟨_, _⟩ hKL
    cases hKL
    rfl
  exact key _ _ h
```

1. After introducing `F` and its field instance, the published theorem
   `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField`
   (M089.001, proved in
   `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`)
   gives `closedFixingSubgroup F (SeparableClosure F) ⊥ = baseField _`.
2. `change` restates it as `intrinsicAbstractBase F = baseField _`; the left
   side is the body of the abbreviation `intrinsicAbstractBase`.
3. The local fact `key` says that two finite abstract fields with equal
   `field` components are equal. It destructs both structures; `cases` on the
   equality of `field` components identifies them, and the remaining
   `finite` components are proofs of the same proposition, so `rfl` closes
   the goal by proof irrelevance.
4. `key` applied to `h` closes the goal: the `field` of
   `intrinsicFiniteAbstractBase F` is definitionally `intrinsicAbstractBase F`,
   and that of `FiniteAbstractField.base _` is definitionally `baseField _`.

No hypothesis, global instance or auxiliary declaration is added. The only
non-Mathlib result used is M089.001, which is proved in the Library.

## Relation to the original proof

The original proof (lines 84–87) performs steps 1 and 2 and then closes the
goal with `FiniteAbstractField.eq_of_field_eq _ _ h` (source row M010.122).
The Library publishes M010.122 only as the statement
`Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eqStatement`,
without a proof. The implemented proof therefore inlines that argument as the
local fact `key`, specialized to `G := intrinsicAbsoluteGalois F`.

The source theorem carries `@[simp]`. The proved theorem here has the published
closed statement as its exact type and omits that attribute.

## Original source

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean>),
SHA-256 `307ae64486245113f5aa94505bbc184048f4daec1af85f89f94f965c57b25e5a`.
The theorem `LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base` has
its docstring at lines 77–78, the `@[simp]` attribute at line 79, its
signature at lines 80–83 and its proof at lines 84–87. The header occupies
lines 1–5.

| Original | Adapted |
| --- | --- |
| Type of `LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base` | Published `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_baseStatement` (Base Statements) |
| Proof of the same theorem | `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base` (this module) |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes: the namespace `LocalClassFieldTheory` is
prefixed with `Langlands.NYLL`; the theorem proves the published closed
proposition instead of restating its signature; the final step of the proof
inlines the unproved M010.122 as described above; the `@[simp]` attribute is
dropped; the proof is placed in its own module `Base/U007/Proofs`; the source
imports are replaced by the single Base Statements import; the source opens
`RamificationTheory CyclicCohomology KummerTheory ClassFormation` and the port
opens only `Langlands.NYLL.ClassFormation`; all other declarations of the
source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0
notice, followed by the dated modification record. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained.

Worker 691 prepared the shared Worker 57 draft for submission on 14 November
2026, retaining its proof term and clarifying this documentation.

This module contains only the M091.007 proof.
