# Targets: the intertwining defect of a linear form vanishes through degree one

This module states the signatures of the four source theorems M351.027,
M351.028, M351.029 and M351.030, the last four declarations of the NYLL module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`. It contains
four proposition definitions (`abbrev`s returning `Prop`); it proves none of
them. Each target is to be proved later by a separate `lean.proof@1` task under
the adapted theorem name listed below.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`,
SHA-256
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`
(943 lines). It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution
supplement is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file, followed by a dated modification notice. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. Worker 495 made the
adaptations listed below. No patch10 edit affects this source module.

## Source context of the four theorems

At the four theorems, the source has the following ambient commands, with no
`section` or later `variable` command in between (lines 28–70):

- `noncomputable section`, `open scoped BigOperators`,
  `attribute [local instance] Classical.propDecidable` (lines 28–31);
- `universe u v w` (line 33), namespaces `LubinTate` and `SameUniformizer`
  (lines 35–36) and `open LocalFieldTheory.DiscreteValuationField` (line 38);
- `variable {K : Type u} [Field K]` (line 68),
  `variable {F : LocalField.{u, v} K} {π : F.valuationSubring}` (line 69) and
  `variable {σ : Type w} [Fintype σ]` (line 70).

Lean includes a section variable in a theorem only when the theorem's header
mentions it (instance variables follow the variables they mention). The
targets below spell out exactly the variables each source header uses, in the
source order.

## Exact targets

Universes are `u`, `v`, `w` as in the source. `F.valuationSubring` is the
valuation subring of the shared adapted local field; `LubinTateSeries F π` is
the published Lubin–Tate series structure. Both are reached through the
imports below.

| Source unit and lines | Target (full Lean name) | Binders, in order | Proposition |
| --- | --- | --- | --- |
| M351.027, `private theorem linearForm_eq_sum_monomial_stabilization`, lines 829–839 | `Langlands.NYLL.PortInternal.M351.d027Statement` | `{K : Type u} [Field K] {F : LocalField.{u, v} K} {σ : Type w} [Fintype σ] (L : σ → F.valuationSubring)` | `linearForm L = ∑ i, MvPowerSeries.monomial (Finsupp.single i 1) (L i)` |
| M351.028, `omit [Fintype σ] in private theorem coeff_defect_sum_linear_monomials_eq_zero [Finite σ]`, lines 841–888 | `Langlands.NYLL.PortInternal.M351.d028Statement` | `{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring} {σ : Type w} [Finite σ] (e ebar : LubinTateSeries F π) (L : σ → F.valuationSubring) (s : Finset σ) (q : σ →₀ ℕ) (_hq : q.degree ≤ 1)` | `MvPowerSeries.coeff q (defect e ebar (∑ i ∈ s, MvPowerSeries.monomial (Finsupp.single i 1) (L i))) = 0` |
| M351.029, `private theorem coeff_defect_linearForm_eq_zero_of_degree_le_one`, lines 890–897 | `Langlands.NYLL.PortInternal.M351.d029Statement` | `{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring} {σ : Type w} [Fintype σ] (e ebar : LubinTateSeries F π) (L : σ → F.valuationSubring) (q : σ →₀ ℕ) (_hq : q.degree ≤ 1)` | `MvPowerSeries.coeff q (defect e ebar (linearForm L)) = 0` |
| M351.030, `theorem two_le_order_defect`, docstring lines 900–901, theorem lines 902–938 | `Langlands.NYLL.LubinTate.SameUniformizer.two_le_order_defectStatement` | `{K : Type u} [Field K] {F : LocalField.{u, v} K} {π : F.valuationSubring} {σ : Type w} [Fintype σ] (e ebar : LubinTateSeries F π) {H : MvPowerSeries σ F.valuationSubring} {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L)` | `(2 : ℕ∞) ≤ (defect e ebar H).order` |

Notes on the binders, each matching the source:

- M351.027 does not mention `π` or any Lubin–Tate series, so the source theorem
  has no `π` argument; neither does `d027Statement`. It keeps `[Fintype σ]`,
  which the finite sums `linearForm L` and `∑ i, …` require.
- M351.028 is preceded by `omit [Fintype σ] in` and adds `[Finite σ]`
  (lines 841–842). The target therefore has `[Finite σ]` and no `Fintype`
  instance. The finite set `s` is arbitrary.
- M351.029 and M351.030 keep the section instance `[Fintype σ]`, needed by
  `linearForm` and `HasLinearTerm`.
- No uniformizer, nontriviality or nonemptiness hypothesis is present or
  added. M351.030 holds for every `H` with prescribed linear term `L`.
- Explicit/implicit status is as in the source: `e`, `ebar`, `L`, `s`, `q` and
  the degree hypothesis are explicit in M351.027–029; in M351.030, `H` and `L`
  are implicit and `hH` explicit.

The adapted names follow the NYLL port plan: source-private theorems become
`Langlands.NYLL.PortInternal.M351.dyyy` (target `dyyyStatement`), and the
public theorem becomes `Langlands.NYLL.LubinTate.SameUniformizer.two_le_order_defect`
(target `two_le_order_defectStatement`).

## Imported definitions

The four targets use only published definitions, reused by Lean name:

- `Langlands.NYLL.LubinTate.SameUniformizer.linearForm L`, the finite sum
  `∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`, and
  `HasLinearTerm H L`, meaning `(2 : ℕ∞) ≤ (H - linearForm L).order`
  (source `LinearTerm.lean`, lines 28–29 and 39–40; module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions`).
- `Langlands.NYLL.LubinTate.SameUniformizer.defect e ebar H`, the difference
  `PowerSeries.subst H e.toPowerSeries - MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`
  of the two sides of the intertwining equation `e(H) = H(ebar(X_i))`
  (source `Intertwiner.lean`, lines 62–66; module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
  which also imports `LubinTateSeries` and the adapted `LocalField`).
- Mathlib's `MvPowerSeries.monomial`, `MvPowerSeries.coeff`,
  `MvPowerSeries.order` (total order, in `ℕ∞`), `Finsupp.single` and
  `Finsupp.degree` (total degree of a multi-index).

In the source these names resolve to the same declarations: `linearForm` and
`HasLinearTerm` are defined only in `LinearTerm.lean`, and `defect` only in
`Intertwiner.lean`, both in namespace `LubinTate.SameUniformizer` of the
source module closure.

## Mathematical meaning

- M351.027: the linear form `∑ L_i X_i` is the sum over `i` of the monomials
  of exponent `e_i` (the multi-index with a single `1` at `i`) and coefficient
  `L_i`.
- M351.028: if `G = ∑_{i ∈ s} L_i X_i` for a finite set `s` of variables, the
  defect `e(G) - G(ebar(X_1), …)` has zero coefficient at every multi-index of
  total degree `0` or `1`.
- M351.029: the same holds for the full linear form `linearForm L`.
- M351.030: whenever `H - ∑ L_i X_i` has total order at least two, the defect
  of `H` has total order at least two, that is, no constant or linear term.

## Adaptations

The following are all modifications to the selected source declarations and
their surrounding interface:

- Split the four theorem signatures from the original 943-line module into
  this focused statement module.
- Rename: the three source-private theorems become the proposition
  definitions `Langlands.NYLL.PortInternal.M351.d027Statement`,
  `d028Statement` and `d029Statement`; the public theorem's namespace is
  prefixed by `Langlands.NYLL` and `Statement` is appended to its name.
- Replace each theorem and its proof by an `abbrev` returning `Prop` with the
  same binders and conclusion. Section variables are written as explicit
  `variable` or definition binders reproducing the source inclusion
  described above. The targets are reducible, as in the published
  Intertwiner targets of the same family, so that the later theorems can be
  used by `rw` and `simp` like the source theorems.
- Rename the unused degree and linear-term hypotheses `hq` and `hH` to `_hq`
  and `_hH` (the proposition body does not use their proofs).
- Replace the source imports
  `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient` and
  `Mathlib.RingTheory.MvPowerSeries.Trunc` by the published focused
  `LinearTerm.Definitions` and `Intertwiner.Definitions` modules. The
  targets mention no declaration of the source modules `RecursiveCoefficient`
  or `Reduction` and no truncation, and the focused module compiles; the
  imports needed by the later proofs belong to the proof tasks.
- Omit `noncomputable section`, `open scoped BigOperators` and
  `attribute [local instance] Classical.propDecidable`. The elaborated
  targets were printed with `pp.explicit` and contain no `Decidable`
  instance, so the omitted local instance does not affect them.
- Replace the module exposition and docstrings with statement-specific
  documentation and this adaptation record.

## Source proof routes (for the later proof tasks)

These describe the source proofs; this module makes no proof claim.

- M351.027: unfold `linearForm` and rewrite each summand `C a * X i` as
  `monomial (single i 1) a` (`MvPowerSeries.monomial_zero_eq_C_apply`,
  `MvPowerSeries.X_def`, `MvPowerSeries.monomial_mul_monomial`). A trial
  proof by this route compiled against these targets.
- M351.028: induction on `s`; the empty case uses that both substitutions of
  `0` vanish, and the insertion step applies the source-private monomial
  response M351.025 (`Langlands.NYLL.PortInternal.M351.d025`) with
  `1 - π ^ 0 = 0`, using the zero constant coefficient of nonconstant
  monomials, M351.021 (`Langlands.NYLL.PortInternal.M351.d021`).
- M351.029: rewrite by M351.027 and apply M351.028 with `s = Finset.univ`.
- M351.030: by `MvPowerSeries.nat_le_order`, reduce to coefficients of
  total degree at most one; there `H` and `linearForm L` agree, so M351.004
  (`coeff_defect_eq_of_coeff_eq_degree_le`), with M347.002 and M347.004 for the
  zero constant coefficients, reduces the claim to M351.029.

## Development verification

The focused module was compiled in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against Library commit
`c40a01345b2f4172fa41e07ff31644b40e695003`, with no warnings or errors.
Separate exact-declaration inspections of all four targets succeeded and
reported `statement_returns_prop: true` with universe parameters `u`, `v`,
`w`. Development compilation and inspection do not establish independent
semantic acceptance or prove any target.
