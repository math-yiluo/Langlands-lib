import Langlands.Global.AdelicEisensteinWeakConstantTermApproximationStatement
import Langlands.Global.AdelicEisensteinConstantTermDecayStatement
import Langlands.Global.AdelicEisensteinConstantTermWeakApproximationStatement
import Langlands.Global.AdelicWavePacketChamberDecayReduction

/-! # Approximation by the weak constant term from the constant term

Delorme 2023 proves Lemma 5.1 by the splitting `φ − φ^w_Q = (φ − φ_Q) + (φ_Q − φ^w_Q)`. Along a
ray `t ↦ exp X exp(tY) ω` of a cone in `𝔞_Q`, the normalized second term
`e^{−tρ(Y)} (φ_Q − φ^w_Q)(exp X exp(tY) ω)` is an exponential polynomial whose exponents have
strictly negative real parts; Lapid's Lemma 3 bounds it, and the factor `e^{tρ(Y)}` is then
reinserted. The first term is bounded by Lemma 3.1. Lemma 5.3 is the analogue for Eisenstein
series. Here the
same splitting `E − ∑ c_q Φ_q = (E − E_Q) + (E_Q − ∑ c_q Φ_q)` derives
`EisensteinWeakConstantTermApproximationStatement` from the decay of `E − E_Q`
(`EisensteinConstantTermDecayStatement`) and the approximation of the constant term `E_Q` on
cones (`EisensteinConstantTermWeakApproximationStatement`):
`eisensteinWeakConstantTermApproximationReduction`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors Langlands.Analysis.Meromorphic PositiveRealTorus

namespace WeakConstantTermApproximation

/-- The arithmetic of the splitting: if `‖X − Y‖ ≤ B₁ S (1 + R)^m e^{−δR}` and
`‖Y − Z‖ ≤ B₂ S e^{−ε₂ R}` with `(1 + R)^m e^{−(δ/2) R} ≤ K₀`, then
`‖X − Z‖ ≤ (max B₁ 0 · max K₀ 0 + max B₂ 0) S e^{−min(ε₂, δ/2) R}`. -/
theorem norm_sub_le_of_split {X Y Z : ℂ} {B₁ B₂ K₀ S R δ ε₂ : ℝ} {m : ℕ} (hR0 : 0 ≤ R)
    (hS0 : 0 ≤ S)
    (hK₀ : (1 + R) ^ m * Real.exp (-(δ / 2 * R)) ≤ K₀)
    (e1 : ‖X - Y‖ ≤ B₁ * S * (1 + R) ^ m * Real.exp (-(((1 : ℕ) : ℝ) * (δ * R))))
    (e2 : ‖Y - Z‖ ≤ B₂ * S * Real.exp (-(ε₂ * R))) :
    ‖X - Z‖ ≤ (max B₁ 0 * max K₀ 0 + max B₂ 0) * S * Real.exp (-(min ε₂ (δ / 2) * R)) := by
  set ε : ℝ := min ε₂ (δ / 2) with hε
  have hexp1 : Real.exp (-(δ * R)) = Real.exp (-(δ / 2 * R)) * Real.exp (-(δ / 2 * R)) := by
    rw [← Real.exp_add]; ring_nf
  have hdec1 : Real.exp (-(δ / 2 * R)) ≤ Real.exp (-(ε * R)) := by
    apply Real.exp_le_exp.mpr
    have : ε ≤ δ / 2 := min_le_right _ _
    nlinarith
  have hdec2 : Real.exp (-(ε₂ * R)) ≤ Real.exp (-(ε * R)) := by
    apply Real.exp_le_exp.mpr
    have : ε ≤ ε₂ := min_le_left _ _
    nlinarith
  have hpoly : (1 + R) ^ m * Real.exp (-(δ / 2 * R)) ≤ max K₀ 0 := hK₀.trans (le_max_left _ _)
  have hpoly0 : 0 ≤ (1 + R) ^ m * Real.exp (-(δ / 2 * R)) := by positivity
  have hB1 : 0 ≤ max B₁ 0 := le_max_right _ _
  have hB2 : 0 ≤ max B₂ 0 := le_max_right _ _
  have hE0 : 0 ≤ Real.exp (-(δ / 2 * R)) := (Real.exp_pos _).le
  have t1 : ‖X - Y‖ ≤ max B₁ 0 * max K₀ 0 * S * Real.exp (-(ε * R)) := by
    refine e1.trans ?_
    simp only [Nat.cast_one, one_mul]
    rw [hexp1]
    calc B₁ * S * (1 + R) ^ m * (Real.exp (-(δ / 2 * R)) * Real.exp (-(δ / 2 * R)))
        = B₁ * S * ((1 + R) ^ m * Real.exp (-(δ / 2 * R))) * Real.exp (-(δ / 2 * R)) := by
          ring
      _ ≤ max B₁ 0 * S * ((1 + R) ^ m * Real.exp (-(δ / 2 * R))) *
            Real.exp (-(δ / 2 * R)) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max B₁ 0 * S * max K₀ 0 * Real.exp (-(ε * R)) := by
          gcongr
      _ = max B₁ 0 * max K₀ 0 * S * Real.exp (-(ε * R)) := by ring
  have t2 : ‖Y - Z‖ ≤ max B₂ 0 * S * Real.exp (-(ε * R)) := by
    refine e2.trans ?_
    gcongr
    exact le_max_left _ _
  calc ‖X - Z‖ = ‖(X - Y) + (Y - Z)‖ := by ring_nf
    _ ≤ ‖X - Y‖ + ‖Y - Z‖ := norm_add_le _ _
    _ ≤ max B₁ 0 * max K₀ 0 * S * Real.exp (-(ε * R)) +
          max B₂ 0 * S * Real.exp (-(ε * R)) := add_le_add t1 t2
    _ = (max B₁ 0 * max K₀ 0 + max B₂ 0) * S * Real.exp (-(ε * R)) := by ring

end WeakConstantTermApproximation

/-- `EisensteinConstantTermDecayStatement` and `EisensteinConstantTermWeakApproximationStatement`
imply `EisensteinWeakConstantTermApproximationStatement`. -/
def EisensteinWeakConstantTermApproximationReductionStatement : Prop :=
  EisensteinConstantTermDecayStatement → EisensteinConstantTermWeakApproximationStatement →
    EisensteinWeakConstantTermApproximationStatement

/-- The splitting `E − ∑ c_q Φ_q = (E − E_Q) + (E_Q − ∑ c_q Φ_q)` on cones. -/
theorem eisensteinWeakConstantTermApproximationReduction :
    EisensteinWeakConstantTermApproximationReductionStatement := by
  intro h1 h2 F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ E D hD hmero hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne hKQ δ hδ t Ω
    hΩ
  obtain ⟨ε₂, m, B₂, k, c, V, L, Φ, hε₂, hc, hL, hshift, hcont, hΦ, happrox⟩ :=
    h2 F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hD hmero
      hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne hKQ δ hδ t Ω hΩ
  obtain ⟨m₁, hm₁⟩ := h1 F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho
    hφ E D hD hmero hreg n e C hC T i ν T₀ j hset hK0 J hJ hJne
  obtain ⟨B₁, hB₁⟩ := hm₁ t Ω hΩ 1
  obtain ⟨K₀, hK₀⟩ := ChamberDecay.exists_one_add_pow_mul_exp_neg_le (half_pos hδ) m₁
  have hε0 : 0 < min ε₂ (δ / 2) := lt_min hε₂ (half_pos hδ)
  have hB₂ : B₂ ≤ max B₁ 0 * max K₀ 0 + max B₂ 0 := by
    have : 0 ≤ max B₁ 0 * max K₀ 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
    linarith [le_max_left B₂ 0]
  refine ⟨min ε₂ (δ / 2), m, max B₁ 0 * max K₀ 0 + max B₂ 0, k, c, V, L, Φ, hε0, hc, hL, hshift,
    hcont, ?_, ?_⟩
  · intro q x hx z hz b hb ω hω
    refine (hΦ q x hx z hz b hb ω hω).trans ?_
    have hσ : 0 ≤ adelicLogHeight F G rho (z * positiveMap F G T i T₀ j b * ω) ^ m :=
      pow_nonneg (zero_le_one.trans (one_le_adelicLogHeight rho _)) m
    have hs : 0 ≤ Real.sqrt (siegelModulus F G T i ν T₀ j b) := Real.sqrt_nonneg _
    gcongr
  · intro x hx z hz b hb ω hω R hR hα
    have hR0 : 0 ≤ R := by
      obtain ⟨β, hβ, -⟩ := hJne
      exact (abs_nonneg _).trans (hR β hβ)
    exact WeakConstantTermApproximation.norm_sub_le_of_split hR0 (Real.sqrt_nonneg _)
      (hK₀ R hR0) (hB₁ x hx z hz b hb ω hω R (δ * R) hR hα) (happrox x hx z hz b hb ω hω R hR hα)

end Langlands.Global
