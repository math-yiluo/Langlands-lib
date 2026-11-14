# `L` is Galois over the decomposition field (NYLL M239.038)

This module proves
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionField_isGalois.{u, v}`
and registers it as a global instance. Its type is exactly the published closed proposition
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionField_isGaloisStatement.{u, v}`
(an `abbrev`), imported from
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Statements`.
This is source unit M239.038, a Prop-valued instance in the source.

## Statement proved

```lean
abbrev decompositionField_isGaloisStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : _root_.ValuationSubring L),
    IsGalois (decompositionField K A) L
```

For every finite-dimensional field extension `L / K` (universes `u`, `v` arbitrary; no
Galois, normality or separability hypothesis on `L / K`) and every valuation subring `A` of
`L`, `L` is a Galois extension (Mathlib's `IsGalois`: normal and separable) of the
decomposition field `decompositionField K A`, the fixed field of the decomposition group
`decompositionGroup K A`.

## Implemented proof and instance registration

```lean
theorem decompositionField_isGalois : decompositionField_isGaloisStatement.{u, v} := by
  intro K L _ _ _ _ A
  exact IsGalois.of_fixed_field L (decompositionGroup K A)

attribute [instance] decompositionField_isGalois
```

After introducing `K`, `L`, the four instances (including `FiniteDimensional K L`) and `A`,
the proof is the source term. Mathlib's `IsGalois.of_fixed_field`
(`Mathlib/FieldTheory/Galois/Basic.lean`) states that for a finite group `G` acting on a
field `E` by ring automorphisms, `E` is Galois over the fixed subfield
`FixedPoints.subfield G E`. Here `G` is the subgroup `decompositionGroup K A` of
`L ≃ₐ[K] L` acting on `L`; it is finite because `L ≃ₐ[K] L` is finite for a
finite-dimensional extension, which instance search supplies from `FiniteDimensional K L`.
The published `decompositionField K A` is `IntermediateField.fixedField (decompositionGroup K A)`,
whose underlying subfield is this fixed subfield, so the term elaborates against the goal by
definitional unfolding.

`attribute [instance] decompositionField_isGalois`, in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`, registers the
theorem as a global instance, as the source's `instance` declaration does; this works
because the target is a reducible `abbrev`. A private test file importing this module
confirmed that `inferInstance` proves `IsGalois (decompositionField K A) L` under
`[FiniteDimensional K L]` for arbitrary `K`, `L`, `A`. The development check of the module
reported no errors or warnings and only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Original source and adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex), *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean#L368-L374),
lines 368–374 (docstring at 368–370, instance signature at 371–373, proof term at 374),
with the section variables at line 32. The source file (752 lines) has SHA-256
`320e356ad4e05be6714d7db6af8ff9c73cb4e3b40f29b59de1cafc597ba8e913`.

| Original | Adapted |
| --- | --- |
| M239.038, `instance RamificationTheory.HilbertRamification.ValuationSubring.decompositionField_isGalois` | `theorem Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring.decompositionField_isGalois` followed by `attribute [instance] decompositionField_isGalois` |
| Section variables (line 32), `[FiniteDimensional K L]` and `A` (line 372) | Introduced by `intro K L _ _ _ _ A` |
| Term `IsGalois.of_fixed_field L (decompositionGroup K A)` (line 374) | Unchanged, under `exact` |
| Six Mathlib imports (lines 7–12) | The single import of the published statement module |
| `noncomputable section` | Omitted |

The docstring is kept verbatim. No other source declaration (in particular none of the
source lines 63–367) is used. Worker 122 made this adaptation on 14 November 2026; the
Lean header records it.

The readable snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

## Consumers

In the source this instance precedes the finite-dimensional declarations over
`decompositionField K A` later in `ValuationSubring.lean`; consumers obtain it by importing
this module.

## Attribution and license

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0 notice
and authorship (assisted by OpenAI Codex), followed by the modification record. The
Library's [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
