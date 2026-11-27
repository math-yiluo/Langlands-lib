# Approximation by the weak constant term from the constant term

Module `Langlands.Global.AdelicEisensteinWeakConstantTermApproximationReduction`, namespace
`Langlands.Global`. It proves

- `eisensteinWeakConstantTermApproximationReduction :
  EisensteinWeakConstantTermApproximationReductionStatement`, where
  `EisensteinWeakConstantTermApproximationReductionStatement` is the implication
  `EisensteinConstantTermDecayStatement → EisensteinConstantTermWeakApproximationStatement →
  EisensteinWeakConstantTermApproximationStatement`;
- `WeakConstantTermApproximation.norm_sub_le_of_split`, the arithmetic of the splitting below.

The two premises are hypotheses of the theorem and are not proved here:

- `EisensteinConstantTermDecayStatement`
  (`Langlands/Global/AdelicEisensteinConstantTermDecayStatement.lean`): Delorme 2023, Lemma 3.1
  (Mœglin–Waldspurger, Lemma I.2.10, for a standard parabolic) applied to `E(φ, λ)` uniformly
  for `λ ∈ i e(C)`: `‖E − E_Q‖(z b ω) ≤ B δ(b)^{1/2} (1 + R)^m e^{−k s}` when
  `|log |β(b)|| ≤ R` for all simple `β` and `s ≤ log |α(b)|` for all `α ∉ J`;
- `EisensteinConstantTermWeakApproximationStatement`
  (`Langlands/Global/AdelicEisensteinConstantTermWeakApproximationStatement.lean`): the
  conclusion of `EisensteinWeakConstantTermApproximationStatement` with the constant term `E_Q`
  in place of `E` in the cone estimate.

## Relation to Delorme's proof

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
`delorme-2023-spectral-theorem-langlands` (published PDF numbering). The proof of Lemma 5.1
(pp.18–19) bounds `φ_Q − φ^w_Q` by Lapid's Lemma 3 on exponential polynomials, applied along
the rays `t ↦ exp X exp(tY) ω` of a cone in `𝔞_Q` to the normalized functions
`e^{−tρ(Y)} (φ_Q − φ^w_Q)(exp X exp(tY) ω)`, whose exponents have strictly negative real parts
(the exponents of the functions themselves are these shifted by `ρ(Y)`), and then "uses
Lemma 3.1 to have a similar bound for `|φ − φ_Q|`. By addition, this gives the Lemma." Lemma 5.3
(pp.19–20) is the analogue for Eisenstein series. The theorem here is this addition for the
Eisenstein series on the cones of `EisensteinWeakConstantTermApproximationStatement`:
`E − ∑ c_q Φ_q = (E − E_Q) + (E_Q − ∑ c_q Φ_q)`.

## The proof of `eisensteinWeakConstantTermApproximationReduction`

Fix the data of `EisensteinWeakConstantTermApproximationStatement`, with `δ > 0`, the threshold
`t` and the compact `Ω`.

1. `EisensteinConstantTermWeakApproximationStatement`, applied to the same data, gives
   `ε₂ > 0`, `m`, `B₂`, `k`, `c`, `V`, `L`, `Φ` with items 1–6 of the target and the cone
   estimate `‖E_Q − ∑_q c_q Φ_q‖ ≤ B₂ δ(b)^{1/2} e^{−ε₂ R}`.
2. `EisensteinConstantTermDecayStatement`, applied to the same data up to `J`, gives `m₁`; for
   the threshold `t`, the compact `Ω` and the exponent `1` it gives `B₁` with
   `‖E − E_Q‖ ≤ B₁ δ(b)^{1/2} (1 + R)^{m₁} e^{−s}`.
3. `ChamberDecay.exists_one_add_pow_mul_exp_neg_le`
   (`Langlands/Global/AdelicWavePacketChamberDecayReduction.lean`) gives `K₀` with
   `(1 + R)^{m₁} e^{−(δ/2) R} ≤ K₀` for `R ≥ 0`.
4. The witnesses are `ε = min(ε₂, δ/2) > 0`, the same `m`, `k`, `c`, `V`, `L`, `Φ`, and
   `B = max(B₁, 0) · max(K₀, 0) + max(B₂, 0)`. Items 1–5 are those of step 1. Item 6 follows
   from that of step 1 because `B₂ ≤ B` and `δ(b)^{1/2} σ(z b ω)^m ≥ 0`
   (`one_le_adelicLogHeight`).
5. Item 7. Let `x`, `z`, `b`, `ω` and `R` satisfy its hypotheses. Since `J ≠ Δ` there is a simple
   root `β`, and `0 ≤ |log |β(b)|| ≤ R`. The cone hypothesis `δ R ≤ log |α(b)|` for `α ∉ J` is
   the hypothesis of step 2 with `s = δ R`, so `‖E − E_Q‖ ≤ B₁ δ(b)^{1/2} (1 + R)^{m₁} e^{−δR}`.
   `WeakConstantTermApproximation.norm_sub_le_of_split` concludes: writing
   `e^{−δR} = e^{−(δ/2)R} e^{−(δ/2)R}`, step 3 and `e^{−(δ/2)R} ≤ e^{−εR}` bound the first
   difference by
   `max(B₁, 0) max(K₀, 0) δ(b)^{1/2} e^{−εR}`; `e^{−ε₂R} ≤ e^{−εR}` bounds the second by
   `max(B₂, 0) δ(b)^{1/2} e^{−εR}`; the triangle inequality adds them.

The proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
