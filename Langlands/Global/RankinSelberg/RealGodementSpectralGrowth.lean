import Langlands.Global.RankinSelberg.RealGodementColumnGrowth
import Langlands.Global.RankinSelberg.RealGodementSpanLie
import Langlands.Global.RankinSelberg.RealGodementSpectralColumn

/-! # Locally uniform right derivatives of entire real Godement columns -/

noncomputable section

open Langlands.Archimedean Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Filter MeasureTheory Metric Set
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

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
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "P" => (Fin n → ℂ)
local notation "Dᵣ" => RealLocalWhittaker.iteratedRightDerivative (t + 1)

/-- Compact tests transport locally uniform lower derivative growth to locally uniform
upper derivative growth. All upper right derivatives retain pointwise spectral holomorphy. -/
def RealGodementSpectralGrowthStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (Ω : Set P), IsOpen Ω →
    ∀ (W : P → G → ℂ) (s : P → ℂ),
      (∀ z ∈ Ω, ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs (W z) ∈
        RealLocalWhittaker.regularFunctions t (-a)) →
      (∀ h, DifferentiableOn ℂ (fun z => W z h) Ω) → DifferentiableOn ℂ s Ω →
      HasLocallyUniformDerivativeGrowth Ω W →
    ∀ (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
    ∀ Φ : supportedSchwartz S,
      let C (z : P) (g : H) := godementLeadingFamily D a Φ.val (W z) p g (s z)
      HasLocallyUniformDerivativeGrowth Ω C ∧
      (∀ z ∈ Ω, ContMDiff (matrixModel ℝ (t + 2)) 𝓘(ℝ, ℂ) ∞ (C z)) ∧
      ∀ Xs g, DifferentiableOn ℂ (fun z => Dᵣ Xs (C z) g) Ω

theorem realGodementSpectralGrowth : RealGodementSpectralGrowthStatement (t := t) (n := n) := by
  intro D a p Ω hΩ W s hReg hW hs hGrowth S hS hRank Φ C
  let F (Ψ : supportedSchwartz S) (z : P) (g : H) := godementLeadingFamily D a Ψ.val (W z) p g (s z)
  let v := (((t + 1 : ℕ) : ℂ) / 2)
  let d (B : Y) := fderiv ℝ (fun A : Y => (Real.log A.det : ℂ)) 1 B
  let detDerivative (B : Y) (z : P) := (s z + v) * d B
  let V (Ψ : supportedSchwartz S) (B : Y) := rectangularRightVariation Ψ.val B S hS Ψ.property
  have hLower (z : P) (hz : z ∈ Ω) : RealUniformWhittaker.HasUniformDerivativeGrowth (W z) := by
    obtain ⟨δ, hδ, N, hN⟩ := hGrowth z hz
    refine ⟨N, fun Xs => ?_⟩
    obtain ⟨C, hC, h⟩ := hN Xs
    exact ⟨C, hC, h z (mem_ball_self hδ)⟩
  have hSmooth (Ψ : supportedSchwartz S) (z : P) (hz : z ∈ Ω) :
      ContMDiff (matrixModel ℝ (t + 2)) 𝓘(ℝ, ℂ) ∞ (F Ψ z) :=
    contMDiff_godementLeadingFamily D a (W z) (hReg z hz) (hLower z hz)
      p (s z) hS hRank Ψ.val Ψ.property
  have hWord (Ψ : supportedSchwartz S) (B : Y) (Xs : List Y) (z : P) (hz : z ∈ Ω) :
      Dᵣ (Xs ++ [B]) (F Ψ z) = detDerivative B z • Dᵣ Xs (F Ψ z) + Dᵣ Xs (F (V Ψ B) z) := by
    have hd := rightDerivative_godementLeadingFamily D a (W z) (hReg z hz) (hLower z hz)
      p (s z) hS hRank Ψ.val Ψ.property B
    change rightDerivative (matrixModel ℝ (t + 2)) B (F Ψ z) =
      detDerivative B z • F Ψ z + F (V Ψ B) z at hd
    have hSm : ContMDiff (matrixModel ℝ (t + 2)) 𝓘(ℝ, ℂ) ∞ (detDerivative B z • F Ψ z) :=
      (((detDerivative B z) • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp
        (hSmooth Ψ z hz)
    have he : Dᵣ (Xs ++ [B]) (F Ψ z) =
        Dᵣ Xs (rightDerivative (matrixModel ℝ (t + 2)) B (F Ψ z)) := by
      simp only [RealLocalWhittaker.iteratedRightDerivative, List.foldr_append, List.foldr_cons, List.foldr_nil]
    rw [he, hd, RealUniformWhittaker.iteratedRightDerivative_add hSm (hSmooth (V Ψ B) z hz),
      RealUniformWhittaker.iteratedRightDerivative_smul (hSmooth Ψ z hz)]
  refine ⟨?_, hSmooth Φ, ?_⟩
  · intro z hz
    obtain ⟨δ, hδ, N, hN⟩ := hGrowth z hz
    let T := ‖s z‖ + 1
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hsAt := (hs.differentiableAt (hΩ.mem_nhds hz)).continuousAt.norm
    have hNearΩ : ∀ᶠ q in 𝓝 z, q ∈ Ω := hΩ.mem_nhds hz
    have hNearδ : ∀ᶠ q in 𝓝 z, q ∈ ball z δ := ball_mem_nhds z hδ
    have hNearT : ∀ᶠ q in 𝓝 z, ‖s q‖ < T := hsAt.eventually_lt continuousAt_const (by dsimp [T]; linarith)
    obtain ⟨ε, hε, hU⟩ := Metric.eventually_nhds_iff_ball.mp (hNearΩ.and (hNearδ.and hNearT))
    let U := ball z ε
    obtain ⟨M, hM⟩ := realGodementColumnFamilyGrowth U t D a p T hT N
    have hBase (Ψ : supportedSchwartz S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ g,
        ‖F Ψ q g‖ ≤ C * realMatrixHeight g ^ M := by
      obtain ⟨C, hC, h⟩ := hM (fun q => W q.val) (fun q => hReg q.val (hU q.val q.property).1)
        (fun Xs => by
          obtain ⟨C, hC, h⟩ := hN Xs
          exact ⟨C, hC, fun q => h q.val (hU q.val q.property).2.1⟩)
        (fun q => s q.val) (fun q => (hU q.val q.property).2.2.le) Ψ.val
      exact ⟨C, hC, fun q hq => h ⟨q, hq⟩⟩
    have hAll (Xs : List Y) (Ψ : supportedSchwartz S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ U, ∀ g,
        ‖Dᵣ Xs (F Ψ q) g‖ ≤ C * realMatrixHeight g ^ M := by
      induction Xs using List.reverseRecOn generalizing Ψ with
      | nil => exact hBase Ψ
      | append_singleton Xs B ih =>
          obtain ⟨C, hC, h⟩ := ih Ψ
          obtain ⟨C', hC', h'⟩ := ih (V Ψ B)
          let A := (T + ‖v‖) * ‖d B‖
          have hA : 0 ≤ A := by dsimp [A]; positivity
          refine ⟨A * C + C', by positivity, fun q hq g => ?_⟩
          have hDetCoeff : ‖detDerivative B q‖ ≤ A := by
            change ‖(s q + v) * d B‖ ≤ (T + ‖v‖) * ‖d B‖
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (norm_nonneg _)
            exact add_le_add_left (hU q hq).2.2.le _
          rw [hWord Ψ B Xs q (hU q hq).1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          calc
            _ ≤ ‖detDerivative B q‖ * ‖Dᵣ Xs (F Ψ q) g‖ + ‖Dᵣ Xs (F (V Ψ B) q) g‖ := by
              simpa only [norm_mul] using norm_add_le (detDerivative B q * Dᵣ Xs (F Ψ q) g) _
            _ ≤ A * (C * realMatrixHeight g ^ M) + C' * realMatrixHeight g ^ M :=
              add_le_add (mul_le_mul hDetCoeff (h q hq g) (norm_nonneg _) hA) (h' q hq g)
            _ = _ := by rw [add_mul, mul_assoc A C]
    exact ⟨ε, hε, M, fun Xs => hAll Xs Φ⟩
  · intro Xs g
    change DifferentiableOn ℂ (fun z => Dᵣ Xs (F Φ z) g) Ω
    induction Xs using List.reverseRecOn generalizing Φ with
    | nil => exact realGodementSpectralColumn D a Φ.val p Ω hΩ W s hReg hW hs hGrowth g
    | append_singleton Xs B ih =>
        have hDetCoeff : DifferentiableOn ℂ (detDerivative B) Ω := (hs.add_const _).mul_const _
        refine ((hDetCoeff.mul (ih Φ)).add (ih (V Φ B))).congr ?_
        intro z hz
        rw [hWord Φ B Xs z hz]
        rfl

end Langlands.Global.RankinSelbergGlobal.RealGodement
