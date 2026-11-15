# Recursive monomial corrections: linear-term and cancellation targets

This module states the signatures of the two theorems M352.003 and M352.004.
It contains proposition definitions; it does not prove them.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCorrection.lean`.
Its SHA-256 is
`87e0549f80ad2537095f3e36ee939774ac0f09d041e36463f6f84e7df1a71edb`.
It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21` under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
registered as `nyll-classfieldtheory-fbd320cd-supplement`.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
Worker 496 made the adaptations listed below. No patch10 edit affects this
source module.

## Exact targets and hypotheses

Both targets are in `Langlands.NYLL.LubinTate.SameUniformizer`. They keep the
source section variables (lines 31–33): `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}`, `{π : F.valuationSubring}` and
`{σ : Type w} [Fintype σ]`, with independent universes `u v w` (line 24).
Each takes, in source order, the explicit uniformizer proof
`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, explicit
`e ebar : LubinTateSeries F π`, implicit
`H : MvPowerSeries σ F.valuationSubring` and `L : σ → F.valuationSubring`,
explicit `hH : HasLinearTerm H L`, explicit `d : σ →₀ ℕ` and explicit
`hd : 2 ≤ d.degree`. All parameters occur in the proposition, so none is
renamed.

| Source unit and lines | Target, relative to the namespace above | Proposition |
| --- | --- | --- |
| M352.003, lines 56–64 | `correctedIntertwiner_hasLinearTermStatement hπ e ebar hH d hd` | `HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L` |
| M352.004, lines 83–93 | `coeff_defect_correctedIntertwiner_eq_zeroStatement hπ e ebar hH d hd` | `MvPowerSeries.coeff d (defect e ebar (correctedIntertwiner hπ e ebar hH d hd)) = 0` |

Meaning. Write `c_d` for the correction coefficient selected in M350.003 and
`H' = H + c_d X^d` for `correctedIntertwiner hπ e ebar hH d hd` (M352.002).

- M352.003 says that `H'` still has prescribed linear term `L`, that is,
  `(2 : ℕ∞) ≤ (H' - linearForm L).order` with
  `linearForm L = ∑ i, C (L i) * X i`.
- M352.004 says that the coefficient of `X^d` in the intertwining defect
  `defect e ebar H' = e(H') - H'(ebar(X_1), …)` vanishes. It concerns the
  single multidegree `d` only; it does not assert that any other defect
  coefficient vanishes.

The imported declarations are the published `HasLinearTerm` and
`linearForm` (LinearTerm definitions), `defect` (Intertwiner definitions),
and `correctedIntertwiner` (the paired RecursiveCorrection definitions).
No hypothesis is added or removed.

## Adaptations and proof boundary

The following are all modifications to the selected source declarations and
their surrounding interface:

- Split the two theorem signatures from the original module into this
  focused statement module.
- Prefix the namespace `LubinTate.SameUniformizer` with `Langlands.NYLL` and
  append `Statement` to both theorem names.
- Replace each theorem and its proof with a `def` returning `Prop`, keeping
  every parameter, binder kind and the conclusion.
- Replace the source imports `RecursiveCoefficient` and
  `DegreeStabilization` by the published focused definition modules named
  above.
- Remove the unused `noncomputable section` and `open scoped BigOperators`,
  and replace the module and theorem docstrings by target documentation.

The source proof routes are: for M352.003, the order bound
`MvPowerSeries.order_monomial` for the inserted monomial together with
`MvPowerSeries.min_order_le_add`; for M352.004, rewriting with the public
monomial response `coeff_defect_add_monomial_eq_of_degree_le` (M351.026,
Task 6089) at `q = d`, the normalized-coefficient law
`uniformizer_mul_normalizedDefectCoefficient` (M350.002) and the scalar
equation `correctionCoefficient_spec` (M350.004), followed by `ring`. Neither
route uses `correctionCoefficient_unique` (M350.005). These descriptions
identify the later proof tasks; this module makes no proof claim. Each exact
theorem is to be routed to a separate `lean.proof@1` task only after its
target has been published.

## Development verification

Compiled in approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) over
Library commit `9ed11fc606807fab34c4852a4e88dbabebba69d1`, which contains the
published paired RecursiveCorrection definitions, with no warnings or errors;
inspection of both targets reported `statement_returns_prop: true` with
universe parameters `u`, `v`, `w` (private diagnostics
`e84f37fa-dcf2-435d-ae3a-9465db95fe5b` and
`7646d371-e780-448f-ba5d-80f438b1e31c`).
Development compilation and inspection do not establish independent semantic
acceptance or prove either target.
