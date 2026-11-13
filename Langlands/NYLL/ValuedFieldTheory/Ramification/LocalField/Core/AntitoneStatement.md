# NYLL M327.010: antitonicity of local upper ramification

This module extracts M327.010, lines 736–748 from Naganori Yamaguchi's *ClassFieldTheory*,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean` (whole-file SHA-256 `d0e79ce27df3b1f7481d2e6c89473f600acaf21f0cf4b678e29ba97a90792ecb`).
The original copyright and author header is preserved. The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
its Apache-2.0 attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found in the Library errata filenames.

## Exact proposition and source correspondence

All definitions below lie in `Langlands.NYLL.RamificationTheory.LocalField`. Each original theorem name is
prefixed with `Langlands.NYLL` and gains the suffix `Statement`. Their full
proposition bodies, including every source parameter and hypothesis, are:

```lean
def localUpperRamificationGroup_antitoneStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Antitone (localUpperRamificationGroup K L)
```

For all Type 0 finite Galois extensions with the source local-field hypotheses on K, the published actual upper filtration is antitone on all real indices. The target requires no supplied target valuation, target topology or extension instance.

## Modifications and dependency boundary

Worker 296 extracted the displayed source signatures into closed `def`s returning
`Prop`: section parameters and theorem binders now occur under `∀` inside the
proposition. The source binder kinds and parameter order are retained, as are all
independent universe levels and hypotheses. The proofs, theorem attributes and
unused surrounding declarations are omitted. The namespace gains the prefix
`Langlands.NYLL`. Source names for the two DVF namespaces are expanded to the
published qualified names; Mathlib constants keep their original meaning.

The source's whole-module imports are replaced by exactly these focused imports:

- `Langlands.NYLL.ValuedFieldTheory.Ramification.LocalField.Core.Definitions`.

These are proposition targets; this module supplies no proof of them. In
particular, it adds no premise assuming its conclusion and no global instance.
The targets refer directly to the published data with the corresponding Lean
names. Compilation and proposition inspection are development evidence only;
independent semantic acceptance and publication remain required.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with hashes `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No feasibility proof patch or unpublished draft is reused here. The target
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
