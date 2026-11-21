import Langlands.Global.RankinSelberg.ComplexSquareZetaReflection
import Langlands.Global.RankinSelberg.ComplexTateProductStripGrowth

/-! # Exponential strip growth of normalized complex square zeta integrals -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexTateProduct (affineParameter complexTateProductEntireFamily complexTateProductStripGrowth)

local instance squareGrowthGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareGrowthGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {r : ℕ}
local notation "Rank" => r.succ
local notation "G" => Langlands.GeneralLinear Rank ℂ
local notation "K" => unitaryCompact ℂ Rank
local notation "Mat" => Matrix (Fin Rank) (Fin Rank) ℂ

/-- Every complex square zeta integral of a standard vector has an entire normalization
of exponential strip growth, with its specified reciprocal L-denominator on the right. -/
def ComplexSquareZetaStripGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ),
    f ∈ complexStandardModule Rank (List.ofFn ds) →
    ∃ (σ : ℝ) (N : ℂ → ℂ), Differentiable ℂ N ∧ HasStripExponentialGrowth N ∧
      ∀ s : ℂ, σ < s.re → Integrable (zetaKernel Φ f s) μ ∧
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ

theorem complexSquareZetaStripGrowth : ComplexSquareZetaStripGrowthStatement (r := r) := by
  intro μ _ κ _ _ ds Φ f hf
  obtain ⟨H, hH⟩ := complexTateProductEntireFamily r
  obtain ⟨c, _, hN⟩ := complexSquareZetaNormalization μ κ 1 H hH
  obtain ⟨hNent, hNagree⟩ := hN ds Φ f hf
  let T := diagonalTest κ 1 Φ f hf.1.continuous
  let m (j : Fin Rank) := (ds j).weight
  let t (j : Fin Rank) := (ds j).exponent
  let N (s : ℂ) := (c : ℂ) * H T m (fun j => s + t j)
  have hP : HasStripExponentialGrowth (fun s => H T m (fun j => s + t j)) := by
    have hu (s : ℂ) : affineParameter t (fun _ => 1) s = fun j => s + t j := by
      funext j
      simp [affineParameter, add_comm]
    simpa only [hu] using complexTateProductStripGrowth r H hH T m t (fun _ => 1)
  have hGrow : HasStripExponentialGrowth N := by
    intro p q
    obtain ⟨C, k, B, hC, hk, hB⟩ := hP p q
    refine ⟨‖(c : ℂ)‖ * C, k, B, by positivity, hk, fun s hp hq hs => ?_⟩
    dsimp only [N]
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB s hp hq hs) (norm_nonneg _)
  obtain ⟨M, hM⟩ := complexSquareZetaConvergence (Nat.succ_pos r) ds
  let D : ℝ := ∑ j, |(t j).re|
  let q := (((Rank : ℂ) - 1) / 2).re
  refine ⟨max ((Rank : ℝ) + M + |q|) D, N, hNent, hGrow, fun s hs => ?_⟩
  have hsM := (le_max_left ((Rank : ℝ) + M + |q|) D).trans_lt hs
  have hsD := (le_max_right ((Rank : ℝ) + M + |q|) D).trans_lt hs
  have hi := hM μ Φ f hf s (by
    rw [Complex.add_re]
    change (Rank : ℝ) + M ≤ s.re + q
    linarith [neg_abs_le q])
  have hpos (j : Fin Rank) : 0 < (s + t j).re := by
    have hD : |(t j).re| ≤ D :=
      Finset.single_le_sum (fun i _ => abs_nonneg (t i).re) (Finset.mem_univ j)
    rw [Complex.add_re]
    linarith [neg_abs_le (t j).re]
  exact ⟨hi, hNagree s hi hpos⟩

/-- Growth transfers to any entire normalization agreeing with the square zeta integral
and its reciprocal denominator on a right half-plane. -/
theorem stripGrowth_of_square_normalization
    (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ)
    (hf : f ∈ complexStandardModule Rank (List.ofFn ds))
    {N : ℂ → ℂ} (hN : Differentiable ℂ N) {σ : ℝ}
    (hEq : ∀ s : ℂ, σ < s.re →
      N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ) :
    HasStripExponentialGrowth N := by
  obtain ⟨τ, M, hM, hG, hτ⟩ := complexSquareZetaStripGrowth μ κ ds Φ f hf
  have hNM : N = M := by
    let s₀ : ℂ := (max σ τ + 1 : ℝ)
    have h₀ : max σ τ < s₀.re := by simp [s₀]
    refine (show AnalyticOnNhd ℂ N univ from fun s _ => hN.analyticAt s).eq_of_eventuallyEq
      (fun s _ => hM.analyticAt s) (z₀ := s₀) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₀] with s hs
    exact (hEq s ((le_max_left _ _).trans_lt hs)).trans (hτ s ((le_max_right _ _).trans_lt hs)).2.symm
  rwa [hNM]

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
