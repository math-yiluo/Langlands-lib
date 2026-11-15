# NYLL M350.001: the normalized defect coefficient

This module adapts exactly the definition `normalizedDefectCoefficient` of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`.
The four other declarations of that source module (M350.002–M350.005) are not
part of this unit.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`.
The source-file SHA-256 is
`bf28f5dfaf69641f687799e72c26590978e6bc0175b24d57a37324fcbf027588`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

| Source unit | Original declaration and lines | Adapted declaration (Lean lines) |
| --- | --- | --- |
| M350.001 | `LubinTate.SameUniformizer.normalizedDefectCoefficient`, 34–43 | `Langlands.NYLL.LubinTate.SameUniformizer.normalizedDefectCoefficient`, lines 37–46 |

The section context of source lines 21–32 is retained: a `noncomputable
section`, universes `u v w`, `open LocalFieldTheory.DiscreteValuationField`,
and the section variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

Inside `namespace Langlands.NYLL.LubinTate.SameUniformizer` the opened
namespace resolves to `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
so `LocalField` is the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`LubinTateSeries F π` is the published
`Langlands.NYLL.LubinTate.LubinTateSeries F π`, `HasLinearTerm` is the
published M347.003 `Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm`
and `defect` is the published M348.005
`Langlands.NYLL.LubinTate.SameUniformizer.defect`. Thus `K`, `F`, `π` and `σ`
are implicit, the field, value-group and variable universes `u`, `v`, `w`
are independent, and `[Fintype σ]` is a section instance used by
`HasLinearTerm` (whose linear form is a finite sum over `σ`).

## Mathematical meaning

Write `O = F.valuationSubring`. For a proof
`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)` that `π` is a
uniformizer of the chosen discrete valuation, two Lubin–Tate series
`e ebar : LubinTateSeries F π`, a multivariable series
`H : MvPowerSeries σ O` with a proof `hH : HasLinearTerm H L` that its linear
term is `∑ i, L i • X_i`, and an exponent `d : σ →₀ ℕ`, the published exact
M349.006 theorem

```lean
uniformizer_dvd_coeff_defect hπ e ebar hH d :
  uniformizer_dvd_coeff_defectStatement hπ e ebar hH d
```

asserts `π ∣ MvPowerSeries.coeff d (defect e ebar H)`, i.e. there is
`c : O` with `coeff d (defect e ebar H) = π * c`. The definition

```lean
normalizedDefectCoefficient hπ e ebar hH d : O :=
  Classical.choose (uniformizer_dvd_coeff_defect hπ e ebar hH d)
```

is the witness `c` chosen by `Classical.choose`: an element of `O` whose
product with `π` is the defect coefficient. The definition records only the
chosen witness; no uniqueness statement is made here. Its defining equation
`π * normalizedDefectCoefficient hπ e ebar hH d = coeff d (defect e ebar H)`
is the separate source theorem M350.002, published as the target
`uniformizer_mul_normalizedDefectCoefficientStatement`. The value depends on
the proofs `hπ` and `hH` only through the proposition they prove (proof
irrelevance), exactly as in the source; `L` is implicit and determined by
`hH`. The definition is noncomputable, as in the source.

## Dependencies and modification record

The single direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.UniformizerDvdCoeffDefect`,
the published module of the exact M349.006 proof
`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_dvd_coeff_defect`
(accepted proof artifact `056d2918-a55c-4dda-ac91-3a24b33c2687` of proof
Task 6750 `3c2b12a8-bb16-4377-9cc6-2a9f32914643`, against the target
`uniformizer_dvd_coeff_defectStatement`, statement artifact
`ac25c50d-47b8-4122-adb4-a2abc02eaa8f` of Task 6071). That target is a
reducible `abbrev` for `π ∣ MvPowerSeries.coeff d (defect e ebar H)`, so
`Classical.choose` applies to the proof directly, as in the source. The
module transitively provides the published `LocalField`, `LubinTateSeries`,
`HasLinearTerm` and `defect`. The source imports the whole source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`; the definition uses
only its theorem `uniformizer_dvd_coeff_defect`. Following the task, the
definition body consumes that exact published proof, not an unproved target.

The complete adaptations are:

1. extraction of M350.001 into this definition-only file, omitting the
   source declarations M350.002 (published separately as a Prop target and
   later proof), M350.003, M350.004 (likewise published separately) and
   M350.005 `correctionCoefficient_unique`, which is not requested;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer` (the source opens and closes them as two nested
   `namespace` commands, retained);
3. the import replacement described above;
4. a modified-file notice in the header and a replaced module docstring.

The noncomputable section, universes, `open`, section variables, the
declaration docstring, name, binders, type and body are otherwise unchanged.
This source module has no patch10 edits. No coercion, simp attribute or
global instance is introduced.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
