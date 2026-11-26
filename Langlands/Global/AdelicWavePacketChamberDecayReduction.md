# The chamber estimate for wave packets from the weak constant term

Module `Langlands.Global.AdelicWavePacketChamberDecayReduction`. It proves

- `wavePacketChamberDecayReduction : WavePacketChamberDecayReductionStatement`, where
  `WavePacketChamberDecayReductionStatement` is the implication
  `EisensteinWeakConstantTermApproximationStatement → EisensteinUniformTemperednessStatement →
  SiegelChamberGeometryStatement → WavePacketChamberDecayStatement`;
- `wavePacketSiegelDecay_of_weakConstantTerm`: the same three propositions and
  `EisensteinImaginaryJointContinuityStatement` imply `WavePacketSiegelDecayStatement`, through
  `wavePacketSiegelDecay_of_reduction` (`Langlands/Global/AdelicWavePacketSiegelDecayReduction.lean`).

The three propositions are hypotheses of these theorems and are not proved here:

- `EisensteinWeakConstantTermApproximationStatement`
  (`Langlands/Global/AdelicEisensteinWeakConstantTermApproximationStatement.lean`): Delorme 2023,
  Lemma 5.3, with the weak constant term (4.3), the relative Eisenstein series (4.1) and
  Proposition 4.1 for the Levi subgroups;
- `EisensteinUniformTemperednessStatement`
  (`Langlands/Global/AdelicEisensteinUniformTemperednessStatement.lean`): Delorme 2023,
  Proposition 4.1;
- `SiegelChamberGeometryStatement` (`Langlands/Global/AdelicSiegelChamberGeometryStatement.lean`):
  the growth of the Iwasawa height of a standard parabolic on cones and the linear upper bound for
  the logarithmic height.

## Relation to Delorme's proof

`WavePacketChamberDecayStatement` is the estimate (5.2) in Delorme's proof of Proposition 5.4
(P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023), pp.20–21), in the
form `‖Θ(z b ω)‖ ≤ B δ(b)^{1/2} σ(z b ω)^{−n}`. Delorme proves Proposition 5.4 by induction on
`dim 𝔞_0^G`. The induction hypothesis is used for the weak constant term `E^w_Q` on a cone around a
direction of `𝔞_Q^{++}`. On such a cone the `𝔞_Q`-component of the torus coordinate is comparable
to the whole coordinate. Fourier decay in that component, together with polynomial growth in the
`M_Q`-component (Proposition 4.1 for `M_Q`), already gives the decay. The proof here therefore
uses no induction: the inputs are the uniform polynomial bounds of
`EisensteinWeakConstantTermApproximationStatement` and `EisensteinUniformTemperednessStatement`.

## Analytic tools

- `Langlands.Analysis.AntiperiodicIntegralDecay.exists_norm_integral_mul_one_add_pow_le`
  (`Langlands/Analysis/AntiperiodicIntegralDecay.lean`): integration by parts in finite
  differences. For `h` smooth with compact support and a direction `v₀` there is `K` with
  `‖∫ h Φ‖ (1 + |Y|)^k ≤ K A` for every continuous `Φ` with `Φ(x + s v₀) = e^{isY} Φ(x)` and
  `0 ≤ A`, `‖Φ‖ ≤ A` on the closed `1`-thickening of the support of `h`; `K` is independent of
  `Φ`, `Y` and `A`.
- `ChamberDecay.exists_norm_integral_mul_one_add_pow_le_of_cone`: fix `h` smooth with compact
  support, a set `C'` containing the closed `1`-thickening of its support, smooth `c_q`,
  directions `v_q`, and constants `ε, c > 0`, `C₁` and `B ≥ 0`. For every `k` there is `K`,
  uniform in `E`, `Φ_q`, `Y`, `R ≥ 0` and `W ≥ 0`, with `‖∫ h E‖ (1 + R)^k ≤ K W` whenever `E`
  and the `Φ_q` are continuous, `‖E − ∑_q c_q Φ_q‖ ≤ B W e^{−εR}` on `C'`, each `Φ_q` satisfies
  `‖Φ_q‖ ≤ B W` on `C'` and the phase law `Φ_q(x + s v_q) = e^{isY} Φ_q(x)`, and
  `c R − C₁ ≤ Y`. The remainder uses `exists_one_add_pow_mul_exp_neg_le`
  (`(1 + R)^k e^{−εR}` is bounded); the components use the previous item with the smooth factor
  `h c_q` and `A = B W`. The bound on each `Φ_q` is needed: the phase law and the remainder bound
  alone do not control the size of the components.
- `ChamberDecay.le_mul_of_decay'`: if `Θ (1 + Y_i)^k ≪_k w s^{m_i}` for finitely many
  quantities `Y_i ≥ 0` and every `k`, and `s ≤ C ∑_i (1 + Y_i)` with `s ≥ 1`, then
  `Θ s^n ≪_n w` for every `n`. The proof takes `k = m + n` and uses
  `(∑_i a_i)^k ≤ (#I)^k ∑_i a_i^k` (`pow_sum_le_card_mul_sum_pow`).
- `ChamberDecay.exists_uniform`: one exponent and, for each `k`, one constant for a finite family
  of monotone bounds.

## Group-theoretic inputs

- `ChamberDecay.isIwasawaCompact_standardMinimal`: a compact `K` that is Iwasawa for one minimal
  parabolic is Iwasawa for the standard minimal parabolic of every algebraic Siegel setup. The
  two are conjugate by a rational point (`minimalParabolicConjugacy`); conjugation preserves the
  Iwasawa property (`IsIwasawaCompact.of_conjugate_map`), which depends only on the image
  (`IsIwasawaCompact.of_range_eq`).
- `ChamberDecay.isIwasawaCompact_standard`: it is then Iwasawa for every standard parabolic
  `Q_J` (`standardParabolicOrder`, `IsIwasawaCompact.of_comp`).
- `ChamberDecay.continuous_imaginary_of_isMeromorphic`: a function meromorphic in coordinates
  whose domain of holomorphy contains the imaginary parameters is continuous on them.
- `ChamberDecay.eisenstein_ambient_phase`: for a rational character `χ` of `G` and
  `v₀ = e^{−1}(p^*(1 ⊗ χ))`, `E(i e(x + s v₀))(g) = ‖χ(g)‖^{is} E(i e(x))(g)`. This is the
  Library's `eisensteinAmbientShift_of_regularParameter` with `eisensteinRegularParameter`,
  applied to the imaginary ambient parameter `i s ⊗ χ`.

## The proof of `wavePacketChamberDecay_of_weakConstantTerm`

Let `Θ = ∫ ∑_q c_q(x) E_q(i e(x)) d(spectralMeasure n)(x)` be a wave packet and fix a setup, a
threshold `t`, a compact `Ω` and `n`. Let `C'` be the `1`-thickening of the union of the supports
of the `c_q`. For points `g = z b ω` (`z ∈ A_G`, `b` in the weak chamber, `ω ∈ Ω`) write
`w = δ(b)^{1/2}`, `s = σ(z b ω)`, `R = ∑_{β ∈ Δ} |log |β(b)||` and
`Y_k = log ‖χ_k(z b ω)‖` for the characters `χ_1, …, χ_r` of
`SiegelChamberHeightComparisonStatement`.

1. **Central characters.** For each `k` and each family `q`, the ambient phase law in the
   direction of `χ_k`, the bound `‖E_q(i e(x))(g)‖ ≤ B_q w s^{m_q}` on `C'` from
   `EisensteinUniformTemperednessStatement`, and the finite-difference estimate give
   `‖∫ c_q E_q‖ (1 + |Y_k|)^N ≪_N w s^{m_q}` for every `N`. Summing over `q`,
   `‖Θ(g)‖ (1 + |Y_k|)^N ≪_N w s^{m}` with `m = ∑_q m_q`.
2. **Cones.** Let `δ₀ = 1/(#Δ + 1)` and, for a point `g`, `J = {β ∈ Δ : log |β(b)| < δ₀ R}`.
   - If `J = Δ`, then `sum_abs_le_of_forall_lt` gives `R ≤ #Δ (#Δ + 1) |log t|`, using
     `log t ≤ log |β(b)|` on the chamber (`log_le_logNormHom_of_mem_chamber`). There the trivial
     bound `‖Θ(g)‖ ≪ w s^m` suffices.
   - Otherwise `J` is a proper subset and `δ₀ R ≤ log |α(b)|` for `α ∉ J`, which is the cone
     condition of `EisensteinWeakConstantTermApproximationStatement` (with
     `|log |β(b)|| ≤ R` for every simple `β`). For each family `q`, applied with the compact
     `C'`, that statement gives `ε`, `m`, `B` and components `c_{q'}`, `Φ_{q'}` with
     `‖E_q(i e(x))(g) − ∑ c_{q'}(x) Φ_{q'}(x, g)‖ ≤ B w e^{−εR}` and
     `‖Φ_{q'}(x, g)‖ ≤ B w s^m` for `x ∈ C'`. Put `W = w s^m`; since `s ≥ 1`, the remainder bound
     has the form `|B| W e^{−εR}` required by the cone estimate, and the component bound is
     `‖Φ_{q'}‖ ≤ |B| W`. `StandardParabolicConeHeightStatement` gives
     `w' ∈ X^*(Q_J) ⊗ ℝ` with `⟨w', H_{Q_J}(g)⟩ ≥ c R − C₁`. By surjectivity of `L_{q'}` choose
     `v_{q'} ∈ V_{q'}` with `L_{q'}(v_{q'}) = w'`. Then the shift law gives
     `Φ_{q'}(x + s v_{q'}, g) = e^{is⟨w', H_{Q_J}(g)⟩} Φ_{q'}(x, g)`, and the cone estimate gives
     `‖∫ c_q E_q‖ (1 + R)^N ≪_N w s^{m}`.
   - The finitely many pairs `(J, q)` are made uniform with `exists_uniform`, and the two cases
     combine to `‖Θ(g)‖ (1 + R)^N ≪_N w s^{m}` for every `N`.
3. **Heights.** `SiegelChamberHeightComparisonStatement`, applied with
   `R' = R + ∑_k |Y_k|`, gives `s ≤ C (1 + R + ∑_k |Y_k|)`.
4. `le_mul_of_decay'` with the indices `Option (Fin r)` (`none ↦ R`, `some k ↦ |Y_k|`) gives
   `‖Θ(g)‖ s^n ≤ B w`, that is `‖Θ(z b ω)‖ ≤ B δ(b)^{1/2} / σ(z b ω)^n`.

The wave packet's parabolic `P` need not contain the minimal parabolic of the setup, and `K` is
the given maximal compact. The two inputs about Eisenstein series are stated for arbitrary
presented `P` and Iwasawa `K`, so no transfer is made here.
