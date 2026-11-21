import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Global.RankinSelberg.RealGodementSpectralColumn

/-! # Gauge estimates with constants uniform over a parameter set -/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalFamily

open Langlands.Archimedean (unitaryCompact)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
  RealRectangularIwasawa
open RealLocalWhittaker (iteratedRightDerivative regularFunctions)

/-- Left covariance under the upper unipotent group with the real trace character of `a`. -/
def HasLeftCharacter {n : ℕ} (a : ℝˣ) (W : Langlands.GeneralLinear (n + 1) ℝ → ℂ) : Prop :=
  ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ, ∀ g,
    W (u * g) = realWhittakerCharacter a u * W g

/-- The simple-root gauge estimate of `RealEqualConvergence.HasGauge`, with one growth
exponent and, for each decay exponent, one constant for all parameters in `S`. -/
def HasUniformGauge {n : ℕ} {P : Type*} (S : Set P)
    (W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ) : Prop :=
  ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
    ∀ (y : Fin (n + 1) → ℝ) (k : unitaryCompact ℝ (n + 1)),
      ‖W p (torus y * (k : Langlands.GeneralLinear (n + 1) ℝ))‖ ≤
        C * Real.exp (-(M : ℝ) * rootPos y + (N : ℝ) * ∑ j, |y j|)

variable {n : ℕ} {P : Type*}

theorem HasLeftCharacter.norm_eq {a : ℝˣ} {W : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasLeftCharacter a W) :
    ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ, ∀ g, ‖W (u * g)‖ = ‖W g‖ := by
  intro u hu g
  rw [hW u hu g, _root_.norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter, one_mul]

theorem HasUniformGauge.mono {S T : Set P} {W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasUniformGauge T W) (hST : S ⊆ T) : HasUniformGauge S W := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  exact ⟨C, hC, fun p hp => hb p (hST hp)⟩

theorem hasUniformGauge_const (S : Set P) {W : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasGauge W) : HasUniformGauge S (fun _ => W) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  exact ⟨C, hC, fun _ _ => hb⟩

/-- The Weyl inverse transpose preserves a uniform gauge. -/
theorem HasUniformGauge.dual {S : Set P} {W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasUniformGauge S W) :
    HasUniformGauge S (fun p => ArchimedeanLocal.dualFunction (n + 1) (W p)) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun p hp y k => ?_⟩
  show ‖ArchimedeanLocal.dualFunction (n + 1) (W p)
    (torus y * (k : Langlands.GeneralLinear (n + 1) ℝ))‖ ≤ _
  rw [RealEqualDualConvergence.dual_torus_mul]
  have h := hb p hp (RealEqualDualConvergence.revNeg y) (RealEqualDualConvergence.weylUnitary k)
  rwa [RealEqualDualConvergence.rootPos_revNeg, RealEqualDualConvergence.sum_abs_revNeg] at h

/-- Right translation by an orthogonal matrix preserves a uniform gauge. -/
theorem HasUniformGauge.translate {S : Set P} {W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : HasUniformGauge S W) {k₀ : Langlands.GeneralLinear (n + 1) ℝ}
    (hk₀ : k₀ ∈ unitaryCompact ℝ (n + 1)) :
    HasUniformGauge S (fun p => ArchimedeanLocal.translateFunction k₀ (W p)) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun p hp y k => ?_⟩
  have h := hb p hp y ⟨(k : Langlands.GeneralLinear (n + 1) ℝ) * k₀,
    (unitaryCompact ℝ (n + 1)).mul_mem k.2 hk₀⟩
  change ‖W p (torus y * (k : Langlands.GeneralLinear (n + 1) ℝ) * k₀)‖ ≤ _
  rwa [mul_assoc]

/-- A family whose right derivatives are regular and share one growth exponent and, for each
derivative word, one constant, has a uniform gauge. -/
theorem hasUniformGauge_of_derivativeGrowth (S : Set P) {a : ℝˣ}
    (W : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ)
    (hreg : ∀ p ∈ S, ∀ Xs, iteratedRightDerivative n Xs (W p) ∈ regularFunctions n a)
    {N : ℕ} (hN : ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ g,
      ‖iteratedRightDerivative n Xs (W p) g‖ ≤ C * realMatrixHeight g ^ N) :
    HasUniformGauge S W := by
  refine ⟨2 * N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := RealWhittakerGauge.gauge_bound_of_derivative_growth_family
    (fun p : S => W p) (fun p => hreg p p.2)
    (fun Xs => by
      obtain ⟨C, h0, h1⟩ := hN Xs
      exact ⟨C, h0, fun p g => h1 p p.2 g⟩) M
  exact ⟨C, hC, fun p hp y k => hb ⟨p, hp⟩ y k⟩

/-- A locally uniform derivative bound becomes uniform on a compact set of parameters. -/
theorem exists_uniform_derivativeGrowth {m : ℕ} {Ω K : Set (Fin m → ℂ)}
    {W : (Fin m → ℂ) → Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hW : RealGodement.HasLocallyUniformDerivativeGrowth Ω W) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ g,
      ‖iteratedRightDerivative n Xs (W z) g‖ ≤ C * realMatrixHeight g ^ N := by
  choose δ hδ N hN using fun z : K => hW z (hKΩ z.2)
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun z : K => ball (z : Fin m → ℂ) (δ z))
    (fun _ => isOpen_ball) (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hδ _)⟩)
  refine ⟨T.sup N, fun Xs => ?_⟩
  choose C hC hb using fun z : K => hN z Xs
  refine ⟨∑ z ∈ T, C z, Finset.sum_nonneg fun z _ => hC z, fun w hw g => ?_⟩
  obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hT hw)
  have hH : 1 ≤ realMatrixHeight g :=
    le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos n) g)
  calc
    _ ≤ C z * realMatrixHeight g ^ N z := hb z w hwz g
    _ ≤ (∑ z ∈ T, C z) * realMatrixHeight g ^ T.sup N :=
      mul_le_mul (Finset.single_le_sum (fun z _ => hC z) hz)
        (pow_le_pow_right₀ hH (Finset.le_sup hz)) (by positivity)
        (Finset.sum_nonneg fun z _ => hC z)

/-- The uniform form of `RealUnequalConvergence.pad_gauge`. -/
theorem HasUniformGauge.pad {r t : ℕ} {S : Set P}
    {W : P → Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : HasUniformGauge S W) (h : t < r)
    (hp : t + 1 ≤ r + 1) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)),
        ‖W p (padGL hp (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)))‖ ≤
          C * Real.exp (-(M : ℝ) * rootPos y + (N : ℝ) * ∑ j, |y j| -
            (M : ℝ) * max (y (Fin.last t)) 0) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun p hpS y k => ?_⟩
  have e : padGL hp (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) =
      torus (RealUnequalConvergence.padVec r y) *
        ((RealUnequalConvergence.padUnitary hp k : unitaryCompact ℝ (r + 1)) :
          Langlands.GeneralLinear (r + 1) ℝ) := by
    rw [map_mul, RealUnequalConvergence.padGL_torus]
    rfl
  rw [e]
  refine (hb p hpS (RealUnequalConvergence.padVec r y)
    (RealUnequalConvergence.padUnitary hp k)).trans (le_of_eq ?_)
  rw [RealUnequalConvergence.rootPos_padVec h, RealUnequalConvergence.sum_abs_padVec h]
  congr 2
  ring

/-- The uniform form of `RealUnequalDualConvergence.gauge_any`. -/
theorem HasUniformGauge.any {S : Set P} {V : P → Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hV : HasUniformGauge S V)
    (hVabs : ∀ p ∈ S, ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ, ∀ g,
      ‖V p (u * g)‖ = ‖V p g‖) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ g,
      ‖V p g‖ ≤ C * Real.exp (-(M : ℝ) * rootPos (alpha g) + (N : ℝ) * ∑ j, |alpha g j|) := by
  obtain ⟨N, hN⟩ := hV
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun p hp g => ?_⟩
  calc
    ‖V p g‖ = ‖V p ((npart g : Langlands.GeneralLinear (n + 1) ℝ) *
        (torus (alpha g) * (kpart g : Langlands.GeneralLinear (n + 1) ℝ)))‖ := by
      rw [← mul_assoc, npart_mul_torus_mul_kpart]
    _ = ‖V p (torus (alpha g) * (kpart g : Langlands.GeneralLinear (n + 1) ℝ))‖ :=
      hVabs p hp _ (npart g).2 _
    _ ≤ _ := hb p hp (alpha g) (kpart g)

/-- The uniform form of `RealUnequalDualConvergence.rect_bound`. -/
theorem HasUniformGauge.rect {r t : ℕ} (h : t < r) {S : Set P}
    {V : P → Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hV : HasUniformGauge S V)
    (hVabs : ∀ p ∈ S, ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      ‖V p (u * g)‖ = ‖V p g‖) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S,
      ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1))
        (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ),
        ‖V p (ArchimedeanLocal.rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x)‖ ≤
          C * Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 +
              ((t : ℝ) + 1) * Real.log (1 + frob x) / 2) +
            (N : ℝ) * (∑ j, |y j| +
              (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Real.log (1 + frob x))) := by
  obtain ⟨N, hN⟩ := hV.any hVabs
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN (((t + 1) + 2 * (t + 1) * (r - (t + 1))) * M)
  refine ⟨C, hC, fun p hp y k x => ?_⟩
  have hα : alpha (ArchimedeanLocal.rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x) =
      fun i => zc y k x (Fin.cast (RealUnequalDualConvergence.rect_size h).symm i) := by
    rw [RealUnequalDualConvergence.rectangularPoint_eq]
    exact alpha_reindex_finCongr (RealUnequalDualConvergence.rect_size h) _
  refine (hb p hp _).trans ?_
  rw [hα, RealUnequalDualConvergence.rootPos_cast (RealUnequalDualConvergence.rect_size h),
    RealUnequalDualConvergence.sum_abs_cast (RealUnequalDualConvergence.rect_size h)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have hdec := decay_le y k x
  have hgr := sum_abs_le y k x
  have hR := rootPos_nonneg (zc y k x)
  push_cast at hdec hgr ⊢
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := mul_le_mul_of_nonneg_left hdec hM
  have h2 := mul_le_mul_of_nonneg_left hgr hN0
  nlinarith

end Langlands.Global.RankinSelbergGlobal.RealUnequalFamily
