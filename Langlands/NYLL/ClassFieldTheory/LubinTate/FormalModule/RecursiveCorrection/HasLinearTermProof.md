# Recursive correction preserves the prescribed linear term

This module proves
`Langlands.NYLL.LubinTate.SameUniformizer.correctedIntertwiner_hasLinearTerm`
with type
`correctedIntertwiner_hasLinearTermStatement hπ e ebar hH d hd`.
The published target and its dependencies are imported without modification.

## Source and attribution

The source is Naganori Yamaguchi (assisted by OpenAI Codex),
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCorrection.lean`,
M352.003, lines 56–81 (proof begins at line 64). The source file SHA-256 is
`87e0549f80ad2537095f3e36ee939774ac0f09d041e36463f6f84e7df1a71edb`.
The readable pinned source is in
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`.

The original copyright, Apache-2.0 and author header is retained verbatim,
followed by Worker 343's dated modification record. The published
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply and are unchanged.
Worker 343 prepared this proof adaptation directly from the pinned source.
Worker 496 prepared the imported published target and recorded the same proof
route in Task 7114's context. No patch10 change affects this source module.

## Exact interface

The theorem retains the source's independent universes `u`, `v`, `w` and the
published target's complete parameter telescope, in this order:

- Implicit `{K : Type u}`, instance `[Field K]`, implicit
  `{F : LocalField.{u, v} K}`, implicit `{π : F.valuationSubring}`,
  implicit `{σ : Type w}` and instance `[Fintype σ]`.
- Explicit `hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)` and
  explicit `e ebar : LubinTateSeries F π`.
- Implicit `H : MvPowerSeries σ F.valuationSubring` and
  `L : σ → F.valuationSubring`.
- Explicit `hH : HasLinearTerm H L`, `d : σ →₀ ℕ` and `hd : 2 ≤ d.degree`.

The conclusion unfolds to
`HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L`.
Here `correctedIntertwiner` is `H + m`, where
`m = monomialCorrection hπ e ebar hH d hd` is the monomial of multidegree
`d` with the selected correction coefficient. The predicate
`HasLinearTerm H L` is the inequality
`(2 : ℕ∞) ≤ (H - linearForm L).order`.
No binder is renamed, reordered, made explicit or implicit, added or removed,
and no additional mathematical hypothesis is imposed.

## Implemented proof

After enabling classical decidability, unfold the target, `correctedIntertwiner`
and `HasLinearTerm`. Cast `hd` to the extended natural numbers with
`exact_mod_cast`.

Unfold `monomialCorrection` and apply `MvPowerSeries.order_monomial`.
If the coefficient is zero, the monomial's order is top, so `le_top` gives
the required lower bound. Otherwise its order is `d.degree`, and the cast
of `hd` supplies the bound. Thus `(2 : ℕ∞) ≤ m.order` in both cases.
This step uses no property of the selected correction coefficient.

Use `ring` to rewrite
`H + m - linearForm L` as `(H - linearForm L) + m`.
The hypothesis `hH` and the correction's order bound give a lower bound of
two for the minimum of the two summands' orders, via `le_min`.
Compose with `MvPowerSeries.min_order_le_add` to obtain the conclusion.
The proof asserts preservation of the prescribed linear term only; it does
not prove any vanishing coefficient of the intertwining defect.

## Imports and adaptations

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection.Statements`.
It transitively supplies the published `correctedIntertwiner`,
`monomialCorrection`, `correctionCoefficient`, `HasLinearTerm`, `linearForm`,
`LocalField`, `LubinTateSeries`, and the Mathlib multivariable power-series
and tactic dependencies. The order lemmas come from
`Mathlib.RingTheory.MvPowerSeries.Order`. The proof invokes no other NYLL theorem.

All adaptations from the selected source theorem are:

- Extract only M352.003 from the original module, omitting its data declarations
  and the separate M352.004 theorem.
- Prefix `LubinTate.SameUniformizer` with `Langlands.NYLL`; the relative
  `open LocalFieldTheory.DiscreteValuationField` resolves under this prefix.
- Replace the source imports `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`
  and `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization` with
  the single published statement-module import above.
- Express the theorem's conclusion using the published `Statement` definition
  and add that definition to the initial `rw`. All subsequent proof commands
  are unchanged from the pinned original.
- Omit the unused `noncomputable section` and `open scoped BigOperators`,
  replace the module documentation, and add the modification record.
  The theorem docstring and parameter declarations retain the source text.

## Development verification

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`),
compilation and theorem inspection succeeded without warnings or errors
(private diagnostic `07ea2b24-bc2f-4090-bc40-dcd59e367a28`). Inspection
reported independent universes `u`, `v`, `w` and only the standard assumptions
`propext`, `Classical.choice`, `Quot.sound`. A separate assignment of the
unapplied theorem to the complete published-target telescope also compiled
without warnings or errors (`732fd1e8-6d92-44e1-8e57-7eb82e8d3f85`).
These development checks do not establish independent acceptance or publication.
