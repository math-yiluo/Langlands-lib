# Substitution for series with a prescribed linear term (NYLL M347.005)

This module proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.hasSubstStatement`
by the theorem
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.hasSubst`.
Its sole import is the statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements`,
which in turn imports the published `Definitions` module of the same
directory. Neither module is changed.

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.LubinTate.SameUniformizer`
and has the target's exact telescope: implicit `R : Type u` with
`[CommRing R]`, implicit `σ : Type v` with `[Fintype σ]` (independent
universes `u` and `v`), implicit `H : MvPowerSeries σ R` and `L : σ → R`, and
the explicit hypothesis `h : HasLinearTerm H L`. Its type is
`HasLinearTerm.hasSubstStatement h`, which unfolds to
`PowerSeries.HasSubst H`.

Here `HasLinearTerm H L` is the published predicate
`(2 : ℕ∞) ≤ (H - linearForm L).order`, where
`linearForm L = ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`.
Mathlib's `PowerSeries.HasSubst H` is the abbreviation
`IsNilpotent (MvPowerSeries.constantCoeff H)`, the condition under which `H`
can be substituted into a one-variable power series.

Mathematically: if `H` agrees with the linear form `∑ L_i X_i` up to terms of
total degree at least two, then `H` has zero constant coefficient, and a
series with zero constant coefficient can be substituted into any
one-variable power series. No local field, valuation, nontriviality or
nonempty-variable hypothesis is used.

## Implemented proof

1. `unfold HasLinearTerm.hasSubstStatement` turns the goal into
   `PowerSeries.HasSubst H`.
2. `horder : 1 ≤ (H - linearForm L).order` lowers the hypothesis
   `2 ≤ (H - linearForm L).order` by transitivity with `(1 : ℕ∞) ≤ 2`,
   proved by `norm_num`.
3. Mathlib's `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` turns
   `horder` into `hconstant : constantCoeff (H - linearForm L) = 0`.
4. `simpa [linearForm] using hconstant` gives
   `hH : MvPowerSeries.constantCoeff H = 0`. In the development environment,
   `simp?` reports the rewrite set `linearForm`, `map_sub`, `map_sum`,
   `map_mul`, `MvPowerSeries.constantCoeff_C`,
   `MvPowerSeries.constantCoeff_X`, `mul_zero`, `Finset.sum_const_zero` and
   `sub_zero`. Thus the constant coefficient of the difference becomes a
   difference, and each summand `C (L i) * X i` of the unfolded linear form
   has constant coefficient `L i * 0 = 0`.
5. Mathlib's `PowerSeries.HasSubst.of_constantCoeff_zero hH` closes the goal;
   zero is nilpotent.

Steps 2–4 prove the statement of M347.004 (zero constant coefficient)
inside this proof; step 4 also re-derives the statement of M347.002 (the
linear form has zero constant coefficient). They are local `have` steps:
no auxiliary declaration, instance or simp attribute is added.

## Pinned source and declaration map

Source: Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean),
unit M347.005 at lines 44 and 56–60. The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`.

| Original (namespace `LubinTate.SameUniformizer`) | Adapted |
| --- | --- |
| Section variables, lines 24–25 and 44 | Same binders, with the universes named `u` and `v` |
| Docstring, lines 56–57 | Kept verbatim |
| Theorem `HasLinearTerm.hasSubst`, lines 58–59 | Same name under `Langlands.NYLL.`; conclusion `HasLinearTerm.hasSubstStatement h` |
| Proof term, line 60: `PowerSeries.HasSubst.of_constantCoeff_zero h.constantCoeff_eq_zero` | Step 1, then steps 2–4 in place of `h.constantCoeff_eq_zero`, then step 5 |
| Proof of `constantCoeff_eq_zero` (M347.004), lines 50–54 | Steps 2–4, with `simpa using` changed to `simpa [linearForm] using` |
| Proof of `constantCoeff_linearForm` (M347.002), line 35: `simp [linearForm]` | Done by the `linearForm` unfolding in step 4 |

## Adaptations

All modifications to the selected source declaration are:

- Prefix the namespace with `Langlands.NYLL`, written as one namespace
  command with a nested `namespace HasLinearTerm`.
- Name the two independent universes `u` and `v` explicitly, matching the
  published statement module, instead of the source's `Type*` binders.
- State the conclusion as the published proposition
  `HasLinearTerm.hasSubstStatement h` and open it with `unfold`.
- Replace the reference to the source theorem `h.constantCoeff_eq_zero`
  (M347.004) by that theorem's own source tactic proof (lines 50–54) as local
  steps. The published theorem
  `Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.constantCoeff_eq_zero`
  is assigned to Task 6353, and
  `Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_linearForm`
  (M347.002) is assigned to Task 6352. Neither is in the Library base
  `c40a01345b2f4172fa41e07ff31644b40e695003` of this work, and a draft is not
  imported. The task context permits another proof route that proves the exact
  published target.
- Because the source's final `simpa using hconstant` relies on the `@[simp]`
  theorem `constantCoeff_linearForm`, add `linearForm` to its simp set. This is
  that theorem's own source proof (line 35).
- Import only the published statement module instead of the source imports
  (`Mathlib.RingTheory.MvPowerSeries.Order` and
  `Mathlib.RingTheory.PowerSeries.Substitution`); the statement module and its
  `Definitions` import provide both.
- Omit the other source declarations of the module (M347.001–M347.004), which
  belong to their own published or assigned units, and the
  `noncomputable section`, which this proof does not need.
- Add a module description, two proof comments and a dated modification
  record.

When the M347.004 theorem is published, the proof could be shortened to the
source's one-line term. The theorem's type does not depend on that choice.

## Attribution, licence and environment

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, including "Naganori Yamaguchi (assisted by OpenAI
Codex)", followed by Worker 465's dated modification record. Worker 465
extracted this proof directly from the pinned original and the published
statement module; there are no project coauthors. The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library and are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The whole
source file has SHA-256
`154a6f23a3514dce4d5b450d51a65db7d3038029c43a56b58f95faecb7d3872d`, recomputed
by Worker 465 on 14 November 2026. The
[port partition](../../../../../../../notes/reuse/nyll-public-port/m337-m360.md#m347)
lists this unit as M347.005 in module M347. No patch10 edit applies.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean
4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). There the module
compiles with no errors or warnings, and the theorem has universe parameters
`u` and `v` and depends only on `propext`, `Classical.choice` and
`Quot.sound`. Compilation is not acceptance: publication under
`lean.proof@1` also requires the Lake build, exact-target and
unchanged-statement checks, independent semantic review and integration.
