# NYLL M351.014: the inserted series has order at least one

`Langlands.NYLL.PortInternal.M351.d014` proves the published proposition
`Langlands.NYLL.PortInternal.M351.d014Statement ebar i`:

```lean
(1 : ℕ∞) ≤ (inVariable ebar i).order
```

Here `ebar : LubinTateSeries F π`, `π : F.valuationSubring`, and `i : σ`.
The parameters are `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}`, `{π : F.valuationSubring}`, and `{σ : Type w}`,
followed by the explicit arguments `(ebar : LubinTateSeries F π) (i : σ)`.
The field, value group, and variable universes are independent. The theorem
requires neither a finite variable type nor a uniformizer hypothesis on `π`.

The series `inVariable ebar i` is `ebar` with `X_i` substituted for its
variable. Its zero constant coefficient implies that every nonzero
coefficient has total degree at least one. The zero series is included:
its order is `⊤`.

## Implemented proof and dependencies

The proof applies the reverse implication of Mathlib's
`MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` to the published theorem
`Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_inVariable ebar i`
(M348.002). The latter supplies
`MvPowerSeries.constantCoeff (inVariable ebar i) = 0`; the former converts
that equality to the required order bound. Both published proposition
targets are reducible abbreviations, so the source proof term is retained
without extra rewriting.

The direct imports are the published `LinearModel.Statements` module,
which supplies `d014Statement` and Mathlib's multivariable order theory,
and `Intertwiner.ConstantCoeffInVariable`, which supplies M348.002.
Their imports supply `inVariable`, `LubinTateSeries`, and `LocalField`.
The proof uses the existing constant coefficient theorem by name.

## Source and attribution

This is the source-private theorem
`LubinTate.SameUniformizer.one_le_order_inVariable_stabilization`,
M351.014, lines 423–428 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file's SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The retained readable file is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the published `notes/errata/`.

## Modification record and license

Worker 792 extracted this theorem on 16 November 2026. Its source-private
name becomes the required public name
`Langlands.NYLL.PortInternal.M351.d014`, and its type is expressed using
the published target `d014Statement`. The original proof term and
elaborated binders are preserved. The source explicitly omits
`[Fintype σ]` for this theorem; this focused module therefore declares no
such section instance. The unused `noncomputable section`, scoped
`BigOperators`, and local `Classical.propDecidable` settings are omitted.
Imports and opened namespaces are adapted to the focused Library modules,
and documentation is added.

The original 2026 copyright, Apache-2.0 release line, and author header
are retained verbatim. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.
