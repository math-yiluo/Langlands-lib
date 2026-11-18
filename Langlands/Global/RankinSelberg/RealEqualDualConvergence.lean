import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.RealFourierSchwartz
import Langlands.Representation.Whittaker.DualTransform

/-! # Convergence and holomorphy of both real equal-rank Rankin–Selberg integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealEqualDualConvergence

open Langlands.Archimedean (unitaryCompact)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence

local instance realDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realDualNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realDualNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realDualQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realDualQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r : ℕ}

/-! ### Inverse transpose on the torus and on the orthogonal group -/

theorem inverseTranspose_torus (y : Fin (r + 1) → ℝ) :
    GeneralLinear.inverseTranspose (r + 1) ℝ (torus y) = torus (-y) := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, ← torus_neg]
  simp only [torus_val, Matrix.diagonal_transpose]

theorem unitary_inv_val (k : unitaryCompact ℝ (r + 1)) :
    (((k : Langlands.GeneralLinear (r + 1) ℝ)⁻¹ : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      ((k : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ).transpose := by
  have hU : ((k : Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈
      Matrix.unitaryGroup (Fin (r + 1)) ℝ := k.2
  have h := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact Units.inv_eq_of_mul_eq_one_right h

theorem inverseTranspose_unitary (k : unitaryCompact ℝ (r + 1)) :
    GeneralLinear.inverseTranspose (r + 1) ℝ (k : Langlands.GeneralLinear (r + 1) ℝ) = k := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, unitary_inv_val, Matrix.transpose_transpose]

theorem weylLong_mem_unitary :
    GeneralLinear.weylLong (r + 1) ℝ ∈ unitaryCompact ℝ (r + 1) := by
  show ((GeneralLinear.weylLong (r + 1) ℝ : Langlands.GeneralLinear (r + 1) ℝ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈ Matrix.unitaryGroup (Fin (r + 1)) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  have h := congrArg Units.val (GeneralLinear.inverseTranspose_weylLong (r + 1) ℝ)
  rw [GeneralLinear.inverseTranspose_coe, GeneralLinear.weylLong_inv] at h
  rw [h, ← Units.val_mul, GeneralLinear.weylLong_mul_self, Units.val_one]

/-- The orthogonal matrix `w k`, for the long Weyl element `w`. -/
def weylUnitary (k : unitaryCompact ℝ (r + 1)) : unitaryCompact ℝ (r + 1) :=
  ⟨GeneralLinear.weylLong (r + 1) ℝ * k, (unitaryCompact ℝ (r + 1)).mul_mem weylLong_mem_unitary k.2⟩

/-- The reversed negative `i ↦ -y_(rev i)`. -/
def revNeg (y : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ := fun i => -y i.rev

theorem weylLong_torus_weylLong (y : Fin (r + 1) → ℝ) :
    GeneralLinear.weylLong (r + 1) ℝ * torus y * GeneralLinear.weylLong (r + 1) ℝ =
      torus (fun i => y i.rev) := by
  apply Units.ext
  ext i j
  rw [GeneralLinear.weylLong_conjugate_entry]
  simp only [torus_val, Matrix.diagonal_apply, Fin.rev_inj]

theorem dual_torus_mul (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (y : Fin (r + 1) → ℝ)
    (k : unitaryCompact ℝ (r + 1)) :
    ArchimedeanLocal.dualFunction (r + 1) W (torus y * (k : Langlands.GeneralLinear (r + 1) ℝ)) =
      W (torus (revNeg y) * (weylUnitary k : Langlands.GeneralLinear (r + 1) ℝ)) := by
  unfold ArchimedeanLocal.dualFunction
  congr 1
  rw [map_mul, inverseTranspose_torus, inverseTranspose_unitary]
  have h : torus (revNeg y) = GeneralLinear.weylLong (r + 1) ℝ * torus (-y) *
      (GeneralLinear.weylLong (r + 1) ℝ)⁻¹ := by
    rw [GeneralLinear.weylLong_inv, weylLong_torus_weylLong]
    rfl
  rw [h]
  show _ = _ * (GeneralLinear.weylLong (r + 1) ℝ * (k : Langlands.GeneralLinear (r + 1) ℝ))
  group

theorem rootPos_revNeg (y : Fin (r + 1) → ℝ) : rootPos (revNeg y) = rootPos y := by
  unfold rootPos revNeg
  simp only [Fin.rev_castSucc, Fin.rev_succ]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin r => max (y i.castSucc - y i.succ) 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply]
  congr 1
  ring

theorem sum_abs_revNeg (y : Fin (r + 1) → ℝ) : ∑ j, |revNeg y j| = ∑ j, |y j| := by
  unfold revNeg
  simp only [abs_neg]
  exact Equiv.sum_comp Fin.revPerm (fun j => |y j|)

/-! ### Hypotheses for the dual integral -/

theorem hasGauge_dual {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : HasGauge W) :
    HasGauge (ArchimedeanLocal.dualFunction (r + 1) W) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun y k => ?_⟩
  rw [dual_torus_mul]
  have h := hb (revNeg y) (weylUnitary k)
  rwa [rootPos_revNeg, sum_abs_revNeg] at h

theorem continuous_dual {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : Continuous W) :
    Continuous (ArchimedeanLocal.dualFunction (r + 1) W) :=
  hW.comp (GeneralLinear.weylInverseTranspose (r + 1) ℝ).continuous

theorem dual_mul_invariant {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g) :
    ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      ArchimedeanLocal.dualFunction (r + 1) W (u * g) * ArchimedeanLocal.dualFunction (r + 1) W' (u * g) =
        ArchimedeanLocal.dualFunction (r + 1) W g * ArchimedeanLocal.dualFunction (r + 1) W' g := by
  intro u hu g
  have h := Langlands.Whittaker.weylInverseTranspose_left_unipotent ⟨u, hu⟩ g
  show W (GeneralLinear.weylInverseTranspose (r + 1) ℝ (u * g)) *
      W' (GeneralLinear.weylInverseTranspose (r + 1) ℝ (u * g)) =
    W (GeneralLinear.weylInverseTranspose (r + 1) ℝ g) *
      W' (GeneralLinear.weylInverseTranspose (r + 1) ℝ g)
  rw [show u * g = (⟨u, hu⟩ : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ).val * g from rfl,
    h]
  exact hinv _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).2 _

theorem fourier_rapidDecay (b : ℝˣ) (Φ : 𝓢(Fin (r + 1) → ℝ, ℂ)) :
    Continuous (realFourierTransform b Φ) ∧ HasRapidDecay (realFourierTransform b Φ) := by
  obtain ⟨Ψ, hΨ⟩ := RealFourierSchwartz.exists_schwartz_eq b Φ
  rw [← hΨ]
  exact ⟨Ψ.continuous, hasRapidDecay_schwartz Ψ⟩

/-! ### Both integrals -/

/-- **Convergence and holomorphy of both integrals.** Under the hypotheses of
`exists_convergence`, for every `b` there is `σ` such that `Ψ(s; W, W', Φ)` and the dual
integral `Ψ(s; W̃, W̃', Φ̂)` (Fourier transform for `realScaledCharacter b`) both converge
absolutely and are holomorphic on `Re s > σ`. -/
theorem exists_pair_convergence (D : RealQuotientMeasureData r) (b : ℝˣ)
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (Φ : 𝓢(Fin (r + 1) → ℝ, ℂ))
    (hW : Continuous W) (hW' : Continuous W')
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g)
    (hgW : HasGauge W) (hgW' : HasGauge W') :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ) s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral b D W W' Φ) {s : ℂ | σ < s.re} := by
  obtain ⟨σ₁, hI₁, hD₁⟩ := exists_convergence D hW hW' Φ.continuous hinv hgW hgW'
    (hasRapidDecay_schwartz Φ)
  obtain ⟨hFc, hFd⟩ := fourier_rapidDecay b Φ
  obtain ⟨σ₂, hI₂, hD₂⟩ := exists_convergence D (continuous_dual hW) (continuous_dual hW') hFc
    (dual_mul_invariant hinv) (hasGauge_dual hgW) (hasGauge_dual hgW') hFd
  refine ⟨max σ₁ σ₂, fun s hs => hI₁ s (lt_of_le_of_lt (le_max_left _ _) hs),
    fun s hs => hI₂ s (lt_of_le_of_lt (le_max_right _ _) hs),
    hD₁.mono fun s (hs : max σ₁ σ₂ < s.re) =>
      (show σ₁ < s.re from lt_of_le_of_lt (le_max_left _ _) hs),
    ?_⟩
  have hD₂' : DifferentiableOn ℂ (realEqualDualIntegral b D W W' Φ) {s : ℂ | σ₂ < s.re} := hD₂
  exact hD₂'.mono fun s (hs : max σ₁ σ₂ < s.re) =>
    (show σ₂ < s.re from lt_of_le_of_lt (le_max_right _ _) hs)


set_option backward.isDefEq.respectTransparency false in
/-- **Both integrals, for uniformly regular functions.** The hypotheses of
`RealEqualConvergenceStatement` give convergence and holomorphy of `Ψ(s; W, W', Φ)` and of the
dual integral for every Fourier parameter `b`, on one common half-plane. -/
theorem exists_pair_convergence_of_regular (D : RealQuotientMeasureData r) {a : ℝˣ} (b : ℝˣ)
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (Φ : 𝓢(Fin (r + 1) → ℝ, ℂ))
    (hreg : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
      RealLocalWhittaker.regularFunctions r a)
    (hgrowth : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N)
    (hreg' : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W' ∈
      RealLocalWhittaker.regularFunctions r (-a))
    (hgrowth' : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W' g‖ ≤ C * realMatrixHeight g ^ N) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ) s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral b D W W' Φ) {s : ℂ | σ < s.re} := by
  have hW : W ∈ RealLocalWhittaker.regularFunctions r a := hreg []
  have hW' : W' ∈ RealLocalWhittaker.regularFunctions r (-a) := hreg' []
  have hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * W' (u * g) = W g * W' g := by
    intro u hu g
    rw [hW.1 u hu g, hW'.1 u hu g]
    calc
      realWhittakerCharacter a u * W g * (realWhittakerCharacter (-a) u * W' g) =
          (realWhittakerCharacter a u * realWhittakerCharacter (-a) u) * (W g * W' g) := by
        ring
      _ = W g * W' g := by rw [realWhittakerCharacter_mul_neg, one_mul]
  exact exists_pair_convergence D b Φ hW.2.1.continuous hW'.2.1.continuous hinv
    (RealWhittakerGauge.exists_gauge_bound hreg hgrowth)
    (RealWhittakerGauge.exists_gauge_bound hreg' hgrowth')

end Langlands.Global.RankinSelbergGlobal.RealEqualDualConvergence

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance realPairStatementGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realPairStatementGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realPairStatementNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realPairStatementNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realPairStatementQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realPairStatementQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- **Convergence and holomorphy of both real equal-rank Rankin–Selberg integrals**
(Jacquet 2009, Theorem 2.1(i) for the integrals on both sides of the equal-rank functional
equation (iii), with holomorphy in the region of convergence). Under the hypotheses of
`RealEqualConvergenceStatement`, for every Fourier parameter `b` there is `σ` such that the
integrands of `Ψ(s; W, W', Φ)` and of `Ψ(s; W̃, W̃', Φ̂)` (with `W̃ = dualFunction W` and `Φ̂`
the Fourier transform for `realScaledCharacter b` and its self-dual measure) are integrable for
`Re s > σ`, and both integrals are holomorphic on `Re s > σ`. These are the first four
conjuncts of `RealJacquet.EqualEquation a b D W W' Φ …`. -/
def RealEqualPairConvergenceStatement : Prop :=
  ∀ (r : ℕ) (D : RealQuotientMeasureData r) (a b : ℝˣ)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
      RealLocalWhittaker.regularFunctions r a) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W' ∈
      RealLocalWhittaker.regularFunctions r (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W' g‖ ≤ C * realMatrixHeight g ^ N) →
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform b Φ) s) D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral b D W W' Φ) {s : ℂ | σ < s.re}

theorem realEqualPairConvergence : RealEqualPairConvergenceStatement :=
  fun _ D _ b _ _ Φ hreg hgrowth hreg' hgrowth' =>
    RealEqualDualConvergence.exists_pair_convergence_of_regular D b Φ hreg hgrowth hreg'
      hgrowth'

end Langlands.Global.RankinSelbergGlobal
