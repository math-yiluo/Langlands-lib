# M350.004: the defining equation of the recursive correction coefficient

This module proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.correctionCoefficient_specStatement`
of
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionSpecStatement`
as the theorem

`Langlands.NYLL.LubinTate.SameUniformizer.correctionCoefficient_spec`.

For a field `K`, a `LocalField.{u, v} K` structure `F`, a uniformizer
`π : F.valuationSubring` of the chosen valuation (`hπ`), Lubin–Tate series
`e ebar : LubinTateSeries F π`, a series `H : MvPowerSeries σ F.valuationSubring`
over a finite type `σ` with prescribed linear term `L` (`hH : HasLinearTerm H L`),
an exponent `d : σ →₀ ℕ` and `hd : 2 ≤ d.degree`, it shows

`(1 - π ^ (d.degree - 1)) * correctionCoefficient hπ e ebar hH d hd = -normalizedDefectCoefficient hπ e ebar hH d`,

with natural-number subtraction `d.degree - 1`. The theorem's binders are those
of the source and the target, and its type is the target applied to `hπ`, `e`,
`ebar`, `hH`, `d` and `hd`.

## Source and attribution

The original is NYLL M350.004 `LubinTate.SameUniformizer.correctionCoefficient_spec`,
lines 77–92 of `Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`
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

The module imports the target module and the published M337.006 proof module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U006.Proofs`.
The proof is the source term

`(Classical.choose_spec (existsUnique_one_sub_uniformizer_pow_mul_eq hπ (by omega : d.degree - 1 ≠ 0) (-normalizedDefectCoefficient hπ e ebar hH d))).1`.

1. From `hd : 2 ≤ d.degree`, `omega` proves the side condition
   `d.degree - 1 ≠ 0`.
2. `existsUnique_one_sub_uniformizer_pow_mul_eq` (M337.006) with this
   exponent and right-hand side `b = -normalizedDefectCoefficient hπ e ebar hH d`
   proves `∃! x, (1 - π ^ (d.degree - 1)) * x = b`.
3. The published definition M350.003 `correctionCoefficient hπ e ebar hH d hd`
   is by definition `Classical.choose` of exactly this proof (the same
   `omega` side proof, equal by proof irrelevance). For `∃! x, p x`, which is
   `∃ x, p x ∧ ∀ y, p y → y = x`, `Classical.choose_spec` gives the
   conjunction for the chosen `x`, and `.1` is its first component
   `(1 - π ^ (d.degree - 1)) * correctionCoefficient hπ e ebar hH d hd = b`.
4. The target unfolds to this equation by definition, which `exact` checks.
   The uniqueness component `.2` is not used (it is the content of the
   unrequested source theorem M350.005).

## Adaptations

- Extract the theorem into its own module, importing the published target
  module (and through it M350.003 and M350.001) and the M337.006 proof module.
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
