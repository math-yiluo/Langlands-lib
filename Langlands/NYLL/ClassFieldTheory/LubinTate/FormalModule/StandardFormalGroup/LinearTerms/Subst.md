# NYLL M354.004: substitution composes linear terms

Worker 331, 16 November 2026; implementation adapted from Worker 497's shared
draft revision 1.

## Exact target and parameters

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.subst` proves
`Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm.substStatement`,
published in module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.LinearTerms.Statements`.
Its conclusion is exactly `substStatement hH hG`.

The parameters, in the target's order and binder kinds, are implicit
`{R : Type*} [CommRing R] {σ : Type w} [Fintype σ] {τ : Type w'} [Fintype τ]`,
implicit `{H : MvPowerSeries σ R} {L : σ → R}`, explicit
`(hH : HasLinearTerm H L)`, implicit
`{G : σ → MvPowerSeries τ R} {M : σ → τ → R}`, and explicit
`(hG : ∀ i, HasLinearTerm (G i) (M i))`. The coefficient ring and the two
variable types have independent universes. Empty variable types and the zero
ring are allowed; there is no local-field, uniformizer, characteristic,
nontriviality, nonemptiness or other added hypothesis.

Here the published definitions are
`linearForm L = ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i` and
`HasLinearTerm H L = ((2 : ℕ∞) ≤ (H - linearForm L).order)`.
The conclusion says that substituting the family `G` into `H` gives a series
with linear coefficient at `j` equal to `∑ i, L i * M i j`.
The target's Lean/Markdown pair and its imports are unchanged.

## Implemented proof

1. Bind the imported theorem `HasLinearTerm.constantCoeff_eq_zero`
   (module `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U004.Proofs`)
   as `hGzero : ∀ i, MvPowerSeries.constantCoeff (G i) = 0`. Its target is a
   `def`, so this explicit equality exposes the conclusion to elaboration.
   `MvPowerSeries.hasSubst_of_constantCoeff_zero` gives `HasSubst G`.
   `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` and `le_iInf` give
   `1 ≤ ⨅ i, (G i).order`, also for an empty index type.
2. `MvPowerSeries.le_order_subst` bounds the order of
   `subst G (H - linearForm L)` below by
   `(⨅ i, (G i).order) * (H - linearForm L).order`.
   Monotonicity of multiplication and `hH` bound this product below by two.
3. `substAlgHom` maps the finite sum defining `linearForm`, giving
   `subst G (linearForm L) = ∑ i, C (L i) * G i`.
   The private lemma `subst_weighted_sum_aux` proves the weighted-sum identity
   `∑ i, C (L i) * linearForm (M i) = linearForm (fun j => ∑ i, L i * M i j)`.
   It uses coefficient extensionality, distribution of coefficients and finite
   sums, `Finset.sum_comm`, and associativity of multiplication; its body is
   the source's private M354.003 proof.
4. Subtract this weighted linear form. Distribute the finite sum and use `ring`
   to obtain `∑ i, C (L i) * (G i - linearForm (M i))`.
   For every multi-index of total degree less than two, each summand has zero
   coefficient by `MvPowerSeries.coeff_C_mul`,
   `MvPowerSeries.coeff_of_lt_order`, and `hG i`.
   `MvPowerSeries.nat_le_order` therefore gives order at least two.
5. Unfold `substStatement` and `HasLinearTerm`. By `subst_sub` and `ring`,
   the required difference is the sum of the error series in steps 2 and 4.
   `MvPowerSeries.min_order_le_add` finishes from their two order bounds.

The private weighted-sum lemma is an internal prerequisite of this proof.
It creates no second public declaration under the separately reserved name
`Langlands.NYLL.PortInternal.M354.d003`. That proof is absent from the Library
base used here, so no unpublished module is imported.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`,
lines 88–167 (signature 90–96, proof 97–167), and the private weighted-sum
lemma at lines 76–86. The file SHA-256 is
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
The retained source is readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`.

Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
folder `n-yamaguchi-0729--ClassFieldTheory/source/`) and
`nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL errata entry is present in this Library's `notes/errata/`.
No patch10 compatibility edit affects this source module.

The original 2026 copyright, Apache-2.0 and author header are retained,
followed by modification records for Workers 497 and 331. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 497 is a coauthor for the reused shared draft.

## Adaptations

- Extract the M354.004 proof and its private M354.003 prerequisite into this
  focused module; prefix the namespace by `Langlands.NYLL`.
- Retain the adapted source theorem name `HasLinearTerm.subst`, the source
  section variables that its type uses, the independent universes, and all
  theorem binders. Omit the unused source variables `K`, `F`, `π`, universes
  `u`, `v`, and the open valuation namespace.
- State the conclusion as the published `substStatement hH hG` and unfold
  that target alongside `HasLinearTerm` near the end of the source proof.
- Import the published target and the published M347.004 proof module instead
  of the source's `RecursiveIntertwiner`, `StandardSeries`, and formal-group
  imports. The imported constant-coefficient theorem replaces the shared
  draft's private `subst_constantCoeff_aux`; bind its result as `hGzero` and
  use it in the two source applications.
- Rename the private source lemma `linearForm_weighted_sum` to
  `subst_weighted_sum_aux`, keeping its proof unchanged. Reference that private
  name in the weighted-sum rewrite; no public M354.003 proof is introduced.
- Omit the unused `noncomputable section` and local classical-decidability
  attribute. Retain the source's scoped big-operator notation and the local
  `classical` steps where finite sums require them. Replace the surrounding
  exposition with documentation of this exact proof.

## Environment and verification

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development check `8c9bfa44-3bf4-4272-ab4e-fdc2498c4c51` compiled this module
with zero errors and warnings. The inspected theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. This check is separate from the independent
semantic review, exact-target validation, and integration required for publication.
