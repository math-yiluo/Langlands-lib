# NYLL M350.002 target: uniformizer times the normalized defect coefficient

This module states, as the Prop-valued definition
`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficientStatement`,
the source theorem `uniformizer_mul_normalizedDefectCoefficient` of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`. It
contains no proof; the exact proof is a separate `lean.proof@1` successor
under the adapted theorem name
`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficient`.

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
| M350.002 | theorem `LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficient`, 45–57 (statement 47–54) | `Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficientStatement`, lines 38–47 |

The source statement is

```lean
theorem uniformizer_mul_normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    π * normalizedDefectCoefficient hπ e ebar hH d =
      MvPowerSeries.coeff d (defect e ebar H)
```

in the section context of source lines 23–32: universes `u v w` and the
section variables `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K} {π : F.valuationSubring}` and
`{σ : Type w} [Fintype σ]`. The target keeps these universes, section
variables (implicit `K`, `F`, `π`, `σ`; instance `[Fintype σ]`), and the
explicit/implicit binders `(hπ) (e ebar) {H} {L} (hH) (d)` in source order,
and its body is exactly the source conclusion. The opened namespace
`LocalFieldTheory.DiscreteValuationField` resolves inside
`Langlands.NYLL.LubinTate.SameUniformizer` to the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.

## Mathematical meaning

With `O = F.valuationSubring`, `hπ` a proof that `π` is a uniformizer of the
chosen discrete valuation, `e ebar : LubinTateSeries F π`, a series
`H : MvPowerSeries σ O` with prescribed linear term `L` (proof `hH`) and an
exponent `d : σ →₀ ℕ`, the proposition says

`π * normalizedDefectCoefficient hπ e ebar hH d = coeff d (defect e ebar H)`

in `O`: the coefficient chosen by M350.001 as a quotient of the `d`-th
coefficient of the intertwining defect `defect e ebar H` (M348.005) by `π`
indeed recovers that coefficient after multiplication by `π`. Here
`normalizedDefectCoefficient` is the published M350.001 definition, and
`MvPowerSeries.coeff d` is Mathlib's coefficient map. No hypothesis beyond
the source's is added, and the conclusion is not weakened.

## Dependencies and modification record

The single direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.NormalizedDefect`,
the published module of M350.001 (artifact
`a4842427-b4a9-4e67-8ae9-c4836038ed7b`, Library commit
`e1fa6f689f9e976eb7574f0dce4453b3b5705ac0`), which provides `normalizedDefectCoefficient`
and transitively the published `LocalField`, `LubinTateSeries`,
`HasLinearTerm`, `defect` and Mathlib's `MvPowerSeries.coeff`. The source
module imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`, which
the signature does not need beyond the definition.

The complete adaptations are:

1. the theorem is replaced by a `def … : Prop` named with the suffix
   `Statement`; its proof is omitted and belongs to the separate proof task;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
3. the import replacement described above; the source's `noncomputable
   section` is not needed for a proposition definition and is omitted;
4. a modified-file notice in the header, a replaced module docstring and a
   docstring naming the target.

All other source declarations of the module are omitted from this file.
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
