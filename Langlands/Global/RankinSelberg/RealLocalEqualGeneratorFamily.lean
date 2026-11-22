import Langlands.Global.RankinSelberg.RealGodementLeadingLeftLaw
import Langlands.Global.RankinSelberg.RealGodementSpanLie
import Langlands.Global.RankinSelberg.RealGodementColumnGrowth
import Langlands.Global.RankinSelberg.RealGodementSpectralGrowth
import Langlands.Global.RankinSelberg.RealLocalEqualFamily
import Langlands.Global.RankinSelberg.RealFourierSchwartz
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual

/-! # Regularity and holomorphy of the real Godement generator family -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator Manifold SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealLocalWhittaker (iteratedRightDerivative regularFunctions)
open RealUnequalFamily (HasLeftCharacter HasUniformGauge hasUniformGauge_const
  hasUniformGauge_of_derivativeGrowth exists_uniform_derivativeGrowth)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) :=
  ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "I" => matrixModel ℝ (t + 2)

/-- For a compactly supported full-row-rank test and a uniform lower coefficient, each
member of the real Godement leading family is a regular Whittaker function with
character `-a`. -/
theorem godementLeadingFamily_mem_regularFunctions (D : RealQuotientMeasureData t) (a : ℝˣ)
    {ds : List RealBlock} {U : G → ℂ} (hU : U ∈ realUniformWhittakerModel t ds (-a))
    (p : Fin 2) (w : ℂ) {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
    (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0) :
    (fun g => godementLeadingFamily D a Φ U p g w) ∈ regularFunctions (t + 1) (-a) := by
  obtain ⟨hReg, hGrowth⟩ := realUniformWhittakerRegularity t ds (-a) U hU
  refine ⟨fun u hu g => realGodementLeadingLeftLaw D a Φ ds U hU p w u hu g,
    contMDiff_godementLeadingFamily D a U hReg hGrowth p w hS hRank Φ hΦ, ?_⟩
  obtain ⟨N, hN⟩ := hGrowth
  obtain ⟨M, hM⟩ := realGodementColumnGrowth t D a p w N
  obtain ⟨C, hC, hb⟩ := hM U hReg hN Φ
  exact ⟨C, M, hC, hb⟩

/-- Every iterated right derivative of a member of the real Godement leading family with a
compactly supported full-row-rank test is a regular Whittaker function with character `-a`. -/
theorem iteratedRightDerivative_godementLeadingFamily_mem (D : RealQuotientMeasureData t)
    (a : ℝˣ) {ds : List RealBlock} {U : G → ℂ} (hU : U ∈ realUniformWhittakerModel t ds (-a))
    (p : Fin 2) (w : ℂ) {S : Set X} (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x)
    (Φ : 𝓢(X, ℂ)) (hΦ : ∀ x ∉ S, Φ x = 0) (Xs : List (Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ)) :
    iteratedRightDerivative (t + 1) Xs (fun g => godementLeadingFamily D a Φ U p g w) ∈
      regularFunctions (t + 1) (-a) := by
  obtain ⟨hReg, hGrowth⟩ := realUniformWhittakerRegularity t ds (-a) U hU
  let C (Ψ : Langlands.Analysis.SchwartzCompactFamilies.supportedSchwartz S) : H → ℂ :=
    fun g => godementLeadingFamily D a Ψ.val U p g w
  let M := Submodule.span ℂ (range C)
  have hMreg : M ≤ regularFunctions (t + 1) (-a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨Ψ, rfl⟩
    exact godementLeadingFamily_mem_regularFunctions D a hU p w hS hRank Ψ.val Ψ.property
  have hStable : ∀ f ∈ M, ContMDiff I 𝓘(ℝ, ℂ) ∞ f ∧
      ∀ B : Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ, rightDerivative I B f ∈ M := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨Ψ, rfl⟩ := hf
      refine ⟨contMDiff_godementLeadingFamily D a U hReg hGrowth p w hS hRank Ψ.val Ψ.property,
        fun B => ?_⟩
      have h := rightDerivative_godementLeadingFamily D a U hReg hGrowth p w hS hRank Ψ.val
        Ψ.property B
      change rightDerivative I B (C Ψ) = _ • C Ψ +
        C (rectangularRightVariation Ψ.val B S hS Ψ.property) at h
      rw [h]
      exact M.add_mem (M.smul_mem _ (Submodule.subset_span ⟨Ψ, rfl⟩))
        (Submodule.subset_span ⟨_, rfl⟩)
    | zero =>
      refine ⟨contMDiff_const, fun B => ?_⟩
      have hz : rightDerivative I B (0 : H → ℂ) = 0 := by
        funext g
        simp only [rightDerivative, Pi.zero_apply, mfderiv_const]
        rfl
      rw [hz]
      exact M.zero_mem
    | add f g _ _ hf hg =>
      refine ⟨hf.1.add hg.1, fun B => ?_⟩
      rw [Archimedean.rightDerivative_add hf.1 hg.1]
      exact M.add_mem (hf.2 B) (hg.2 B)
    | smul c f _ hf =>
      refine ⟨((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf.1,
        fun B => ?_⟩
      rw [Archimedean.rightDerivative_smul hf.1]
      exact M.smul_mem c (hf.2 B)
  have hAll : ∀ Ys : List (Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ),
      iteratedRightDerivative (t + 1) Ys (C ⟨Φ, hΦ⟩) ∈ M := by
    intro Ys
    induction Ys with
    | nil => exact Submodule.subset_span ⟨⟨Φ, hΦ⟩, rfl⟩
    | cons B Ys ih => exact (hStable _ ih).2 B
  exact hMreg (hAll Xs)


/-! ### Holomorphy of the equal-rank integrals of the generator family -/

private theorem hasLeftCharacter_dual {c : ℝˣ} {W : H → ℂ} (hW : HasLeftCharacter c W) :
    HasLeftCharacter (-c) (ArchimedeanLocal.dualFunction (t + 2) W) := by
  intro u hu g
  change W (GeneralLinear.weylInverseTranspose (t + 2) ℝ (u * g)) =
    realWhittakerCharacter (-c) u * W (GeneralLinear.weylInverseTranspose (t + 2) ℝ g)
  rw [Langlands.Whittaker.weylInverseTranspose_left_unipotent (u := ⟨u, hu⟩),
    hW _ (Langlands.Whittaker.reflectedUnipotent ⟨u, hu⟩).property,
    RealUnequalPairConvergence.realWhittakerCharacter_reflected]

/-- On every disk of leading exponents there is a common spectral half-plane on which the
real equal-rank integrals of the generator family and of its Weyl inverse-transpose dual
converge absolutely and are jointly holomorphic in the exponent and the spectral variable. -/
def RealLocalEqualGeneratorFamilyStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a b : ℝˣ)
    (ds es : List RealBlock) (U : G → ℂ), U ∈ realUniformWhittakerModel t ds (-a) →
  ∀ (V : H → ℂ), V ∈ realUniformWhittakerModel (t + 1) es a →
  ∀ (p : Fin 2) (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
  ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) →
  ∀ (φ : 𝓢(Fin (t + 2) → ℝ, ℂ)) (R : ℝ),
    let L (z : ℂ) : H → ℂ := fun g => godementLeadingFamily D a Φ U p g z
    ∃ σ : ℝ,
      (∀ z ∈ Metric.ball (0 : ℂ) R, ∀ s : ℂ, σ < s.re →
        Integrable (realEqualIntegrand (L z) V φ s) D'.measure ∧
        Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (t + 2) (L z))
          (ArchimedeanLocal.dualFunction (t + 2) V) (realFourierTransform b φ) s) D'.measure) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => realEqualIntegral D' (L x.1) V φ x.2)
        (Metric.ball (0 : ℂ) R ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => realEqualDualIntegral b D' (L x.1) V φ x.2)
        (Metric.ball (0 : ℂ) R ×ˢ {s : ℂ | σ < s.re})

set_option maxHeartbeats 1000000 in
theorem realLocalEqualGeneratorFamily : RealLocalEqualGeneratorFamilyStatement (t := t) := by
  intro D D' a b ds es U hU V hV p S hS hRank Φ hΦ φ R L
  obtain ⟨hReg, hGrowth⟩ := realUniformWhittakerRegularity t ds (-a) U hU
  obtain ⟨hVreg, hVgrowth⟩ := realUniformWhittakerRegularity (t + 1) es a V hV
  have hVr : V ∈ regularFunctions (t + 1) a := hVreg []
  have hVg : RealEqualConvergence.HasGauge V := RealWhittakerGauge.exists_gauge_bound hVreg hVgrowth
  -- the generator family on the parameter space `Fin 1 → ℂ`
  let C₁ (z : Fin 1 → ℂ) : H → ℂ := fun g => godementLeadingFamily D a Φ U p g (z 0)
  have hLoc : HasLocallyUniformDerivativeGrowth (univ : Set (Fin 1 → ℂ)) (fun _ => U) := by
    intro z _
    obtain ⟨N, hN⟩ := hGrowth
    refine ⟨1, one_pos, N, fun Xs => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN Xs
    exact ⟨C, hC, fun _ _ h => hb h⟩
  have hSpec := (realGodementSpectralGrowth (t := t) (n := 1)) D a p univ isOpen_univ (fun _ => U)
    (fun z => z 0) (fun _ _ => hReg) (fun _ => differentiableOn_const _)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).differentiable.differentiableOn)
    hLoc S hS hRank ⟨Φ, hΦ⟩
  obtain ⟨N, hN⟩ := exists_uniform_derivativeGrowth hSpec.1 (isCompact_closedBall (0 : Fin 1 → ℂ) R)
    (subset_univ _)
  let E := ℂ × ℂ
  let T : Set E := Metric.ball (0 : ℂ) R ×ˢ univ
  have hT : IsOpen T := Metric.isOpen_ball.prod isOpen_univ
  let Wf (x : E) : H → ℂ := L x.1
  have hball (x : E) (hx : x ∈ T) : (fun _ : Fin 1 => x.1) ∈ Metric.closedBall (0 : Fin 1 → ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const]
    exact (Metric.mem_ball.mp hx.1).le.trans_eq' (by rw [dist_zero_right])
  have hWreg (x : E) : ∀ Xs, iteratedRightDerivative (t + 1) Xs (Wf x) ∈ regularFunctions (t + 1) (-a) :=
    iteratedRightDerivative_godementLeadingFamily_mem D a hU p x.1 hS hRank Φ hΦ
  have hWgauge : HasUniformGauge T Wf :=
    hasUniformGauge_of_derivativeGrowth T Wf (fun x _ => hWreg x) (N := N) (fun Xs => by
      obtain ⟨C, hC, hb⟩ := hN Xs
      exact ⟨C, hC, fun x hx g => hb _ (hball x hx) g⟩)
  have hWleft (x : E) : HasLeftCharacter (-a) (Wf x) := (hWreg x []).1
  have hVleft : HasLeftCharacter (-(-a)) V := by
    rw [neg_neg]
    exact hVr.1
  have hWc (x : E) : Continuous (Wf x) := (hWreg x []).2.1.continuous
  have hWd (g : H) : DifferentiableOn ℂ (fun x : E => Wf x g) T :=
    ((differentiable_godementLeadingFamily D a Φ hU p g).comp differentiable_fst).differentiableOn
  obtain ⟨σ₁, hI₁, hD₁⟩ := realLocalEqualFamily (-a) D' T Wf (fun _ => V) Prod.snd φ hT
    differentiable_snd hWleft (fun _ => hVleft) hWc (fun _ => hVr.2.1.continuous) hWd
    (fun _ => differentiableOn_const _) hWgauge (hasUniformGauge_const T hVg)
  obtain ⟨φd, hφd⟩ := RealFourierSchwartz.exists_schwartz_eq b φ
  let Wd (x : E) : H → ℂ := ArchimedeanLocal.dualFunction (t + 2) (Wf x)
  let Vd : H → ℂ := ArchimedeanLocal.dualFunction (t + 2) V
  have hArg : Continuous (GeneralLinear.weylInverseTranspose (t + 2) ℝ) :=
    (GeneralLinear.weylInverseTranspose (t + 2) ℝ).continuous
  obtain ⟨σ₂, hI₂, hD₂⟩ := realLocalEqualFamily (-(-a)) D' T Wd (fun _ => Vd) Prod.snd φd
    hT differentiable_snd (fun x => hasLeftCharacter_dual (hWleft x))
    (fun _ => by simpa only [neg_neg] using hasLeftCharacter_dual hVleft)
    (fun x => (hWc x).comp hArg) (fun _ => hVr.2.1.continuous.comp hArg)
    (fun g => hWd (GeneralLinear.weylInverseTranspose (t + 2) ℝ g))
    (fun _ => differentiableOn_const _) hWgauge.dual (hasUniformGauge_const T hVg).dual
  refine ⟨max σ₁ σ₂, fun z hz s hs => ?_, ?_, ?_⟩
  · have h₁ := hI₁ (z, s) ⟨⟨hz, mem_univ _⟩, (le_max_left _ _).trans_lt hs⟩
    have h₂ := hI₂ (z, s) ⟨⟨hz, mem_univ _⟩, (le_max_right _ _).trans_lt hs⟩
    rw [hφd] at h₂
    exact ⟨h₁, h₂⟩
  · exact hD₁.mono fun x hx => ⟨⟨hx.1, mem_univ _⟩,
      show σ₁ < x.2.re from (le_max_left σ₁ σ₂).trans_lt hx.2⟩
  · have h := hD₂.mono fun (x : E) (hx : x ∈ Metric.ball (0 : ℂ) R ×ˢ {s : ℂ | max σ₁ σ₂ < s.re}) =>
      (⟨⟨hx.1, mem_univ _⟩, show σ₂ < x.2.re from (le_max_right σ₁ σ₂).trans_lt hx.2⟩ :
        x ∈ T ∩ {v : E | σ₂ < v.2.re})
    rw [hφd] at h
    exact h

end Langlands.Global.RankinSelbergGlobal.RealGodement
