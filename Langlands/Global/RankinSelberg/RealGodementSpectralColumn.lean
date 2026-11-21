import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Global.RankinSelberg.RealGodementColumnParameter

/-! # Holomorphy of the real Godement column with a varying lower coefficient -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t n : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "P" => (Fin n → ℂ)

/-- Near each spectral point, one exponent works for all right derivatives and all parameters.
The norm constant may depend on the derivative word and the neighborhood. -/
def HasLocallyUniformDerivativeGrowth (Ω : Set P) (W : P → G → ℂ) : Prop :=
  ∀ z ∈ Ω, ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
    ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ ball z δ, ∀ h,
      ‖RealLocalWhittaker.iteratedRightDerivative t Xs (W q) h‖ ≤ C * realMatrixHeight h ^ N

private theorem differentiableAt_integral_of_integrable_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (F : P → A → ℂ) (s₀ : P) {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ a, DifferentiableOn ℂ (fun z => F z a) (ball s₀ δ))
    (hMeas : ∀ z ∈ ball s₀ δ, AEStronglyMeasurable (F z) μ) {B : A → ℝ} (hB : Integrable B μ)
    (hBound : ∀ z ∈ ball s₀ δ, ∀ a, ‖F z a‖ ≤ B a) :
    DifferentiableAt ℂ (fun z => ∫ a, F z a ∂μ) s₀ := by
  let r := δ / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hsub : ball s₀ r ⊆ ball s₀ δ := ball_subset_ball (by dsimp [r]; linarith)
  have hloc : ∀ z ∈ ball s₀ r, closedBall z r ⊆ ball s₀ δ := by
    intro z hz y hy
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hy
    have h := dist_triangle y z s₀
    dsimp [r] at hz hy
    linarith
  have hB' : Integrable (fun a => B a / r) μ := hB.div_const _
  have hD (z : P) (hz : z ∈ ball s₀ r) (a : A) :
      ‖fderiv ℂ (fun q => F q a) z‖ ≤ B a / r :=
    norm_fderiv_le isOpen_ball (hF a) hr (hloc z hz) (fun y hy => hBound y (hloc z hz hy) a)
  have hM : ∀ z ∈ ball s₀ r, AEStronglyMeasurable (F z) μ := fun z hz => hMeas z (hsub hz)
  have h₀ := mem_ball_self hδ (x := s₀)
  have hFs₀ : Integrable (F s₀) μ := hB.mono' (hMeas s₀ h₀) (ae_of_all _ (hBound s₀ h₀))
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (F := F) (F' := fun z a => fderiv ℂ (fun q => F q a) z) (bound := fun a => B a / r)
    (ball_mem_nhds s₀ hr) (Filter.Eventually.mono (ball_mem_nhds s₀ hr) hM) hFs₀ ?_
    (ae_of_all _ fun a z hz => hD z hz a) hB' ?_).differentiableAt
  · exact aestronglyMeasurable_fderiv F hr hM
      (fun a => (hF a).differentiableAt (ball_mem_nhds s₀ hδ))
  · exact ae_of_all _ fun a z hz => ((hF a).differentiableAt
      (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt

/-- The column Mellin integral is holomorphic when the lower coefficient and the exponent
vary holomorphically and the lower right derivatives have locally uniform growth. -/
theorem differentiableOn_columnMellinFamily (μ : Measure G) [μ.IsHaarMeasure] (a : ℝˣ)
    (Φ : 𝓢(X, ℂ)) (p : ℕ) {Ω : Set P} (hΩ : IsOpen Ω) (W : P → G → ℂ) (s : P → ℂ)
    (hReg : ∀ z ∈ Ω, ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs (W z) ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hW : ∀ h, DifferentiableOn ℂ (fun z => W z h) Ω) (hs : DifferentiableOn ℂ s Ω)
    (hGrowth : HasLocallyUniformDerivativeGrowth Ω W) :
    DifferentiableOn ℂ (fun z => ∫ h, columnMellinIntegrand a Φ (W z) p (s z) h ∂μ) Ω := by
  let F (z : P) := columnMellinIntegrand a Φ (W z) p (s z)
  have hF (h : G) : DifferentiableOn ℂ (fun z => F z h) Ω :=
    (((hW (columnRepresentative h)).const_mul _).mul_const _).mul ((hs.mul_const _).cexp)
  have hMeas (z : P) (hz : z ∈ Ω) : AEStronglyMeasurable (F z) μ := by
    have hB := continuous_columnMellinBase ((hReg z hz []).2.1.continuous) a Φ p
    have hS := ((Complex.continuous_ofReal.comp (continuous_logAbsDet (t := t))).const_mul (s z)).cexp
    exact (hB.mul hS).aestronglyMeasurable
  intro z hz
  obtain ⟨δ, hδ, N, hN⟩ := hGrowth z hz
  let m := ((t + 1 : ℕ) : ℝ)
  let R := |(s z).re - m| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsAt := (hs.differentiableAt (hΩ.mem_nhds hz)).continuousAt
  have hS : ContinuousAt (fun q => |(s q).re - m|) z :=
    ((Complex.continuous_re.continuousAt.comp hsAt).sub continuousAt_const).abs
  have hΩNear : ∀ᶠ q in 𝓝 z, q ∈ Ω := hΩ.mem_nhds hz
  have hδNear : ∀ᶠ q in 𝓝 z, q ∈ ball z δ := ball_mem_nhds z hδ
  have hNear : ∀ᶠ q in 𝓝 z, q ∈ Ω ∧ q ∈ ball z δ ∧ |(s q).re - m| < R :=
    hΩNear.and (hδNear.and (hS.eventually_lt continuousAt_const (by dsimp [R]; linarith)))
  obtain ⟨ε, hε, hBall⟩ := Metric.eventually_nhds_iff_ball.mp hNear
  let U := ball z ε
  have hsub : U ⊆ Ω := fun q hq => (hBall q hq).1
  obtain ⟨q, _, hSem⟩ := exists_columnMellin_family_seminorm (ι := U) μ a N R hR
  obtain ⟨B, hB, _, hBounds⟩ := hSem (fun y => W y.val) (fun y => hReg y.val (hsub y.property))
    (fun Xs => by
      obtain ⟨C, hC, hBound⟩ := hN Xs
      exact ⟨C, hC, fun y => hBound y.val (hBall y.val y.property).2.1⟩)
  have hBound (y : P) (hy : y ∈ U) (h : G) : ‖F y h‖ ≤ q Φ * B h :=
    hBounds ⟨y, hy⟩ Φ p (s y) (hBall y hy).2.2.le h
  exact (differentiableAt_integral_of_integrable_bound μ F z hε
    (fun h => (hF h).mono hsub) (fun y hy => hMeas y (hsub hy)) (hB.const_mul (q Φ))
    hBound).differentiableWithinAt

/-- With a locally uniformly bounded holomorphic lower family, the real leading Godement
column is holomorphic in all spectral parameters, at each fixed upper group element. -/
def RealGodementSpectralColumnStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (Φ : 𝓢(X, ℂ)) (p : Fin 2) (Ω : Set P),
    IsOpen Ω → ∀ (W : P → G → ℂ) (s : P → ℂ),
      (∀ z ∈ Ω, ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs (W z) ∈
        RealLocalWhittaker.regularFunctions t (-a)) →
      (∀ h, DifferentiableOn ℂ (fun z => W z h) Ω) → DifferentiableOn ℂ s Ω →
      HasLocallyUniformDerivativeGrowth Ω W → ∀ g : H,
        DifferentiableOn ℂ (fun z => godementLeadingFamily D a Φ (W z) p g (s z)) Ω

theorem realGodementSpectralColumn : RealGodementSpectralColumnStatement (t := t) (n := n) := by
  intro D a Φ p Ω hΩ W s hReg hW hs hGrowth g
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let e := weylLong (t + 2) ℝ * g
  let v : ℂ := ((t : ℂ) + 1) / 2
  have hM := differentiableOn_columnMellinFamily μ a (rectangularTranslate 1 e Φ) p.val hΩ W
    (fun z => s z + (t : ℂ) / 2) hReg hW (hs.add_const _) hGrowth
  have hDet : DifferentiableOn ℂ (fun z => determinantWeight (charData p (s z)) v e) Ω := by
    rw [funext fun z => determinantWeight_exponent_shift p v (s z) 0 e]
    simp only [sub_zero]
    exact ((hs.mul_const _).cexp).const_mul _
  exact hDet.mul hM

end Langlands.Global.RankinSelbergGlobal.RealGodement
