# Coercion targets for the standard integer-ring equivalence (M335.006–007)

This module states, as Prop-valued definitions and without proofs, the two
coercion lemmas of the source for
`Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv` (M335.005). Both
take the source section parameters: `K : Type` explicit and
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
instance-implicit. `𝒪[K]` is Mathlib's scoped `ValuativeRel` notation for
`Valuation.integer (ValuativeRel.valuation K)`.

- `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv_apply_coeStatement K x`,
  for `x : 𝒪[K]`: coercing `standardLocalFieldIntegerEquiv K x`, an element
  of `(standardLocalField K).valuationSubring`, to `K` gives `(x : K)`.
- `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv_symm_apply_coeStatement K x`,
  for `x : (standardLocalField K).valuationSubring`: coercing
  `(standardLocalFieldIntegerEquiv K).symm x`, an element of `𝒪[K]`, to `K`
  gives `(x : K)`.

Each is a `def` returning `Prop`; the proposition is exactly the source
theorem's type.

## Source

Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`
(SHA-256 `88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`),
section variables at lines 37–38. Registered sources:
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Unit | Source theorem (lines; declaration line) | Library target |
| --- | --- | --- |
| M335.006 | `LubinTate.standardLocalFieldIntegerEquiv_apply_coe` (91–98; 94) | `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv_apply_coeStatement` |
| M335.007 | `LubinTate.standardLocalFieldIntegerEquiv_symm_apply_coe` (100–107; 103) | `Langlands.NYLL.LubinTate.standardLocalFieldIntegerEquiv_symm_apply_coeStatement` |

## Modifications

- Each theorem becomes a Prop-valued `def` whose body is the source theorem's
  type verbatim, with the namespace prefix `Langlands.NYLL` and the
  `Statement` suffix. The parameters, their binder kinds and order, and the
  docstrings are unchanged.
- The source proofs (`rfl` in both cases) and `@[simp]` attributes are not
  part of a target; the proofs remain separate units.
- Imports. The source module's six NYLL imports are replaced by the single
  M335.005 module `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv`.
  The source's unused `open` commands are omitted, and the targets are
  outside the source's `noncomputable section`, which they do not need.
- Replacement module documentation and a modification notice in the header.

The original copyright, Apache-2.0 and author lines are retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.

This file proves nothing.
