# NYLL M351.004: finite-degree continuity of intertwining defects

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_le`
proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_leStatement`.
For a field `K : Type u`, the shared local-field package
`F : LocalField.{u,v} K`, an arbitrary `π : F.valuationSubring`, a variable
type `σ : Type w` with `[Finite σ]`, and `e ebar : LubinTateSeries F π`,
two series `H H' : MvPowerSeries σ F.valuationSubring` with zero constant
coefficients and equal coefficients through total degree `m` have equal
defect coefficients at every exponent `d` with `d.degree ≤ m`.
The defect is the published expression `e(H) - H(ebar(X_i))_i`.
The theorem preserves all target binders, their order, and the independent
universes `u v w`; its stated result is exactly
`coeff_defect_eq_of_coeff_eq_degree_leStatement e ebar hH hH' hcoeff hd`.

## Source and correspondence

Naganori Yamaguchi (assisted by OpenAI Codex),
[`ClassFieldTheory`, pinned source](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.
The original theorem is
`LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_le`,
docstring lines 135–142, signature 143–153 and proof 154–194.
The source-file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
It is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL-specific erratum is present in the Library's `notes/errata/`.

The implemented proof follows the original truncation route. Its local
`htrunc` is the reverse implication of source M351.001 (lines 58–66).
Its local `hleft` and `hright` are the source-private M351.002 and M351.003
proofs (lines 81–107 and 116–133), specialized to `k = m + 1`.
These facts are proved inside this theorem; the module declares none of the
three theorem names reserved for the sibling proof tasks.

## Implemented proof

Let `k = m + 1`. Polynomial extensionality proves
`H.truncTotal k = H'.truncTotal k`: below degree `k`, apply the coefficient
agreement hypothesis; at larger degrees, both truncated coefficients vanish.

On the left side of the defect, the zero constant coefficients of `H` and
`H'` give `PowerSeries.HasSubst` witnesses. View one-variable substitution
as multivariable substitution with variable type `Unit`. Apply
`MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le`
to replace each inner series by its truncation at `k`, and use `htrunc`.

On the right side, each `inVariable ebar i` has zero constant coefficient
by `PowerSeries.constantCoeff_subst_eq_zero`, the zero constant coefficient
of `MvPowerSeries.X i`, and the field
`LubinTateSeries.constantCoeff_eq_zero` of `ebar`. Apply
`MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst`
to replace the outer series by its truncation at `k`, and use `htrunc`.

Unfold `defect` and use `map_sub` for the linear truncation map. The two
substitution equalities imply equality of the defect truncations.
Finally `d.degree ≤ m` gives `d.degree < k`, and
`MvPowerSeries.coeff_truncTotal` identifies the coefficients of the
truncations with those of the original defects.

## Imports and adaptations

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements`.
It supplies the exact target, the published `LocalField`, `LubinTateSeries`,
`inVariable` and `defect` definitions, and Mathlib's substitution and
total-degree truncation API through its imports. No pending sibling proof
module is imported, and no published source file is changed.

Worker 488's shared draft isolated the target theorem and prefixed its
namespace with `Langlands.NYLL`. Worker 517 replaced that draft's pending
sibling imports with the target module and inlined their needed arguments
as local facts. The computation of the constant coefficient of
`inVariable` uses Mathlib directly instead of the original M348.002 theorem.
Polynomial extensionality is applied explicitly with `MvPolynomial.ext`,
keeping the coefficient equalities in the valuation subring.
The unused source section `[Fintype σ]`, `noncomputable section` and
`open scoped BigOperators` are omitted; `[Finite σ]` remains as in the
source theorem. The local classical decidability attribute is retained.
The result is written as the published proposition, with new explanatory
docstrings and modification notices.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
