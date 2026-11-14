# NYLL M347.004: `HasLinearTerm.constantCoeff_eq_zero`

Worker 464, 14 November 2026. This file proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.constantCoeff_eq_zeroStatement`
(module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements`)
with the required theorem
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.constantCoeff_eq_zero`.

## Exact statement

The theorem has the target's parameters, in the same order and binder kinds:
implicit `{R : Type u} [CommRing R] {σ : Type v} [Fintype σ]` with independent
universes `u` and `v`, implicit `{H : MvPowerSeries σ R} {L : σ → R}`, and the
explicit hypothesis `(h : HasLinearTerm H L)`. Its conclusion is
`constantCoeff_eq_zeroStatement h`, which unfolds to
`MvPowerSeries.constantCoeff H = 0`. Here `HasLinearTerm H L` is the published
predicate `(2 : ℕ∞) ≤ (H - linearForm L).order`, and `linearForm L` is the
published finite sum `∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`.
No local-field, nontriviality, nonempty-variable or other hypothesis is added.
The target's Lean/Markdown pair and the definitions it imports are unchanged.

In words: if a multivariable power series over a commutative ring differs from
the linear form `∑ i, L i • X i` by a series of total order at least two, then
its constant coefficient is zero.

## Implemented proof

1. `change` replaces the target proposition by its definition,
   `MvPowerSeries.constantCoeff H = 0`.
2. `horder`: since `(1 : ℕ∞) ≤ 2` (by `norm_num`), transitivity with `h`,
   which is definitionally `(2 : ℕ∞) ≤ (H - linearForm L).order`, gives
   `(1 : ℕ∞) ≤ (H - linearForm L).order`.
3. `hconstant`: the forward direction of Mathlib's
   `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` turns `horder` into
   `MvPowerSeries.constantCoeff (H - linearForm L) = 0`.
4. `hlinear`: `MvPowerSeries.constantCoeff (linearForm L) = 0`, proved by
   unfolding `linearForm` and simplifying. The constant coefficient is a ring
   homomorphism, so it maps the finite sum of products to the sum of
   `L i` times the constant coefficient of `X i`, which is zero.
5. `simpa [hlinear] using hconstant` rewrites the constant coefficient of the
   difference as `constantCoeff H - constantCoeff (linearForm L)`, replaces the
   second term by zero using `hlinear`, and closes the goal.

Development compilation reported no errors or warnings. The inspected theorem
depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. It introduces no new axiom, global instance or simp lemma.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`, lines 44–54
(theorem `LubinTate.SameUniformizer.HasLinearTerm.constantCoeff_eq_zero`;
signature at lines 48–49, proof at lines 50–54), with ambient section
variables at lines 24–25. The original file SHA-256 is
`154a6f23a3514dce4d5b450d51a65db7d3038029c43a56b58f95faecb7d3872d`.
Its readable retained path is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Copyright 2026 Naganori Yamaguchi; original authors Naganori Yamaguchi
(assisted by OpenAI Codex). The original copyright, Apache-2.0 and author
header is retained in the Lean file, followed by a modification record. The
unchanged license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Adaptations

All modifications relative to source lines 44–54 and their context:

- The nested source namespaces `LubinTate` and `SameUniformizer` become the
  single namespace `Langlands.NYLL.LubinTate.SameUniformizer`; the theorem
  stays in its `HasLinearTerm` sub-namespace under its original name.
- The source's two `Type*` binders (lines 24–25) are written with explicit
  independent universes `u` and `v`, as in the published target.
- The conclusion is the published proposition
  `constantCoeff_eq_zeroStatement h` instead of the source's literal
  `MvPowerSeries.constantCoeff H = 0`; the two are definitionally equal, and
  the proof begins with `change` to expose the latter.
- The source's final `simpa using hconstant` (line 54) relies on the global
  simp lemma `constantCoeff_linearForm` (source lines 32–35). Its exact
  Library theorem (M347.002, owned by Task 6352, expected module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U002.Proofs`)
  was not published at this workspace's Library base. The proof therefore
  establishes that fact locally as `hlinear`, with the source's own proof
  `simp [linearForm]` (line 35), and passes it to `simpa`. No public duplicate
  of that theorem is introduced. This route is permitted by the task context.
- Steps 2 and 3 above are the source's lines 50–53 verbatim.
- The source imports and module are replaced by the single import of the
  published target module, which itself imports the published definitions and
  the source's two Mathlib imports. The unneeded `noncomputable section` wrapper
  is omitted. A module docstring for this focused proof replaces the source
  module exposition; the theorem docstring (lines 46–47) is retained.
- The neighbouring source declarations (lines 28–40 and 56–60) are not part of
  this module.

## Environment

Development checks used approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Development compilation does not
constitute acceptance; publication requires the proof policy's independent
review, Lake build and exact-target checks.
