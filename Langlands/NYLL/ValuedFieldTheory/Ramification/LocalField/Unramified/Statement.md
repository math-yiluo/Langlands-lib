# NYLL M329.002: trivial upper groups for actual unramified extensions

This module extracts M329.002, signature lines 55–68, proof through line 79 from Naganori Yamaguchi's *ClassFieldTheory*,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Unramified.lean` (whole-file SHA-256 `81d609ee80761316740480f408d238ad59883f4790d713337fcb195c5d3f7717`).
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
def localUpperRamificationGroup_eq_bot_of_unramifiedValuationStatement : Prop :=
  ∀ (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (t : ℝ) (ht : 0 ≤ t),
    localUpperRamificationGroup K L t = ⊥
```

For Type 0 fields K and L with both source local-field structures, finite Galois algebra, supplied valuation extension, integral-closure and finite integer-module instances, and the published actual IsUnramifiedValuedExtension class, every nonnegative-index local upper group is trivial. All source hypotheses, including the separate integral-closure hypothesis, are retained. The published unramified class permits independent universes; it is specialized to universe zero here, exactly as in this source theorem.

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
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions`.

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
