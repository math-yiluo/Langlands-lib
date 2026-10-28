# Proof of the valuation-shell decomposition of multiplicative Haar integrals

`Langlands.RankinSelberg.valuationShellIntegration :
ValuationShellIntegrationStatement.{uF}` proves the published proposition
`Langlands.RankinSelberg.ValuationShellIntegrationStatement` from the module
`Langlands.Representation.RankinSelberg.ValuationShellIntegrationStatement`.
The universe `uF` is arbitrary. The theorem's type is the whole Library
statement. It keeps every quantified prime `p` (with `Fact p.Prime`), field
`F : PadicField.{uF} p` and supplied realization `T : F.TopologicalData`, and it
adds no hypothesis.

The proof installs the statement's instances: `T.topology`, `T.valuativeRel`,
`T.localField`, `borel F.Carrier` with its `BorelSpace` witness, and
`borel F.Carrierˣ` with its `BorelSpace` witness. It then introduces the
statement's local definitions unchanged:

- `μ = localMultiplicativeHaar F.Carrier`, the actual normalized measure;
- `K`, the actual integral units `integralUnits (ValuativeRel.valuation F.Carrier).integer`;
- `S n = {a | T.ord (a : F.Carrier) = n}`, the actual shells.

No replacement measure or supplied decomposition is used.

## The uniformizer

The witness is the published unit `π = LocalFactor.PadicAbelian.uniformizerUnit T`,
the specified uniformizer `T.uniformizer` regarded as a unit. Its order is one
by the published `uniformizerUnit_ord`. For every `n : ℤ` and every unit `a`,
the order of `π ^ n * a` is `n + T.ord a`. This follows from the published
`ord_mul` (both factors are nonzero), `Units.val_zpow_eq_zpow_val` and
`ord_zpow`.

## Shell geometry

- `S 0 = K`: a unit `a` lies in `K` exactly when `a` and `a⁻¹` are both
  integers (`mem_integralUnits`). By `normalizedAbs_le_one_iff_mem_integers`
  and `normalizedAbs_of_ne_zero`, these conditions say `q ^ (-ord a) ≤ 1` and
  `q ^ (ord a) ≤ 1` (using `ord_inv`), where `q = T.residueCardinality > 1`
  (`residueCardinality_gt_one`). By `zpow_le_one_iff_right₀`, they say
  `0 ≤ ord a` and `ord a ≤ 0`, that is, `ord a = 0`.
- From this and the order formula for `π ^ n * u`: `u ∈ K` exactly when
  `π ^ n * u ∈ S n`.
- `S n = (fun u => π ^ n * u) '' K`: the image lies in `S n` by the previous
  item. Conversely, if `a ∈ S n` then `(π ^ n)⁻¹ * a` lies in `K`, and its
  translate by `π ^ n` is `a`.
- Openness: `S n` is the preimage of `{n}` under the order map on units. That
  map is continuous into the discrete integers by the published
  `continuous_ord_units`. Measurability follows from openness, since the
  measurable structure is Borel.
- Compactness: `K` is compact by the published `integralUnits_isCompact`. Its
  `T2Space` hypothesis comes from `localField_t2` in
  [Measures](Measures.md): a
  nonarchimedean local field is Hausdorff, via its uniform additive group
  structure. `S n` is the image of `K` under the continuous map `u ↦ π ^ n * u`.
- Mass one: by `Set.image_mul_left`, `S n` is the preimage of `K` under
  `a ↦ (π ^ n)⁻¹ * a`. Left invariance of the Haar measure
  (`measure_preimage_mul`) and the published normalization
  `localMultiplicativeHaar_integerUnits` give `μ (S n) = μ K = 1`.
- Absolute value: for `a ∈ S n`, `normalizedAbs_of_ne_zero` gives
  `T.normalizedAbs a = q ^ (-T.ord a) = q ^ (-n)`.
- Two shells with different indices are disjoint because the order is a
  function. Every unit `a` lies in `S (T.ord a)`, so the shells cover the units.

## Translating shell integrals

The generic lemma `setIntegral_comp_mul_left_of_mem_iff` holds for a group `G`
with `MeasurableMul G`, a left-invariant measure `μ`, and functions with values
in a real Banach space `E`. Let `K` and `S` be measurable sets with
`u ∈ K ↔ g * u ∈ S` for every `u`. Then

```text
∫ u in K, f (g * u) ∂μ = ∫ a in S, f a ∂μ.
```

Write both set integrals as integrals of indicators (`integral_indicator`).
Rewrite the right side with Mathlib's `integral_mul_left_eq_self`. The two
indicator integrands then agree pointwise, by the hypothesis on `K` and `S`. No
measurability of `f` is needed.

The main proof applies this lemma with `g = π ^ n` and `S = S n`. It uses
`f` for complex integrands and `‖f‖` for real ones. So each shell integral
`∫ a in S n, f a ∂μ` equals `∫ u in K, f (π ^ n * u) ∂μ`.

## Local integrability

Let `f` be continuous. Then `u ↦ f (π ^ n * u)` is continuous, and `K` is
compact and measurable. Mathlib's `ContinuousOn.integrableOn_compact'` then
gives `IntegrableOn (fun u => f (π ^ n * u)) K μ`. The needed finiteness on
compact sets comes from the published `IsHaarMeasure` instance for `μ`.
`IntegrableOn f (S n) μ` follows the same way from compactness of `S n`.

## Integrability criterion

After the shell translation, the criterion reads
`Integrable f μ ↔ Summable (fun n => ∫ a in S n, ‖f a‖ ∂μ)`.

- If `f` is integrable, then so is `‖f‖`, on `⋃ n, S n = univ`. Mathlib's
  `hasSum_integral_iUnion` for the countable, measurable, pairwise disjoint
  family `S` gives a `HasSum` of the shell norm integrals, hence summability.
- Conversely, `f` is integrable on every shell (local integrability above).
  Mathlib's `integrableOn_iUnion_of_summable_integral_norm` then gives
  integrability on `⋃ n, S n = univ`, that is, `Integrable f μ`
  (`integrableOn_univ`).

Neither side is assumed; the criterion is proved for every continuous `f`.

## Integral identity

If `f` is integrable, `hasSum_integral_iUnion` applies to `f` itself. It gives
`HasSum (fun n => ∫ a in S n, f a ∂μ) (∫ a in ⋃ n, S n, f a ∂μ)`. Since the union
is `univ`, the right side is `∫ a, f a ∂μ` (`Measure.restrict_univ`). After the
shell translation, this gives the summability of
`n ↦ ∫ u in K, f (π ^ n * u) ∂μ` and the identity
`∫ a, f a ∂μ = ∑' n, ∫ u in K, f (π ^ n * u) ∂μ` (`HasSum.tsum_eq`).

## Provenance and attribution

Worker 871 wrote this proof. Its mathematics is the standard change of
variables described in the statement's Markdown. That Markdown cites
Jacquet–Piatetski-Shapiro–Shalika, *Rankin-Selberg Convolutions* (1983),
printed p. 392, display (6) and the following paragraphs. The Lean route is
specific to this formalization.

Two steps adapt arguments from the published module
`Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof`,
authored by Worker 235:

- the rewrite chain proving `S 0 = K` follows that module's private lemma
  `ord_eq_zero_iff_mem_integralUnits`;
- the description of a shell as a uniformizer translate follows its proof of
  compactness of a fixed-order shell.

Those two helpers are private, so this module restates their arguments.
The Hausdorff step reuses the existing `localField_t2` proof in
`RankinSelberg.Measures`, exposed as a public theorem during integration.
No unpublished draft was reused.

## Checks

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
module with no errors or warnings. Inspecting
`Langlands.RankinSelberg.valuationShellIntegration` showed only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The module contains no `sorry`,
`admit` or new axiom. Compilation does not establish acceptance. Independent
review, the Lake build and the exact-target check remain required.
