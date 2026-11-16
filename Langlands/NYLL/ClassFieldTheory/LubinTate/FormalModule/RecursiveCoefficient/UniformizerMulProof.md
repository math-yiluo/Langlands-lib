# M350.002: the uniformizer times the normalized defect coefficient

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficientStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.UniformizerMulStatement`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficient`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation (`hπ`), Lubin–Tate series
`e ebar : LubinTateSeries F π`, a series `H : MvPowerSeries σ F.valuationSubring`
over a finite type `σ` with prescribed linear term `L` (`hH : HasLinearTerm H L`)
and an exponent `d : σ →₀ ℕ`, it shows

`π * normalizedDefectCoefficient hπ e ebar hH d = MvPowerSeries.coeff d (defect e ebar H)`.

The theorem's binders are those of the source and the target, and its type is
the target applied to `hπ`, `e`, `ebar`, `hH` and `d`.

## Source and attribution

The original is NYLL M350.002 `LubinTate.SameUniformizer.uniformizer_mul_normalizedDefectCoefficient`,
lines 45–57 of `Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`
in Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709` (file SHA-256
`bf28f5dfaf69641f687799e72c26590978e6bc0175b24d57a37324fcbf027588`), readable in
registered source `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The Lean
file keeps the original copyright, Apache-2.0 and author header;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply unchanged. This source
module has no patch10 edits.

## Implemented proof

The module imports the target module and the published M349.006 proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.UniformizerDvdCoeffDefect`.
The proof is the source term

`(Classical.choose_spec (uniformizer_dvd_coeff_defect hπ e ebar hH d)).symm`.

1. `uniformizer_dvd_coeff_defect hπ e ebar hH d` (M349.006) proves
   `π ∣ MvPowerSeries.coeff d (defect e ebar H)` in the commutative ring
   `F.valuationSubring`; divisibility unfolds to
   `∃ c, MvPowerSeries.coeff d (defect e ebar H) = π * c`.
2. The published definition M350.001 `normalizedDefectCoefficient hπ e ebar hH d`
   is by definition `Classical.choose` of exactly this proof, so
   `Classical.choose_spec` gives
   `MvPowerSeries.coeff d (defect e ebar H) = π * normalizedDefectCoefficient hπ e ebar hH d`.
3. `Eq.symm` turns this into the target equation; the target unfolds to it by
   definition, which `exact` checks.

## Adaptations

- Extract the theorem into its own module, importing the published target
  module (and through it M350.001) and the M349.006 proof module.
- Prefix the namespaces `LubinTate` and `SameUniformizer` by `Langlands.NYLL`;
  the opened namespace `LocalFieldTheory.DiscreteValuationField` resolves to
  the published `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- State the theorem's type as the published target applied to its parameters;
  the proof term and docstring are the source's.
- Replace the module documentation; drop the unneeded `noncomputable section`.

Worker 341 adopted Worker 490's Task 6080 draft revision 1 on
2026-11-16, preserving its proof term and attribution and checking it against
the current published target. No mathematical adaptation was added.

## Development verification

Compiled with no errors or warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`); the theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`. Compiling it does not
show that it has been accepted or published.
