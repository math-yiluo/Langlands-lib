import Langlands.Global.RankinSelberg.ComplexSquareZetaStripGrowth
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Global.Factors.CuspidalPairPoleSymmetry
import Langlands.Automorphic.AssociatedGammaCuspidalEquation

/-! # Exponential strip growth through the complex equal-rank Jacquet expansion -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.LocalFactor.Archimedean ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel archimedeanComplexQMeasurable
  archimedeanComplexQBorel

private theorem stripGrowth_sum {ι : Type*} [Fintype ι] {f : ι → ℂ → ℂ}
    (hf : ∀ i, HasStripExponentialGrowth (f i)) :
    HasStripExponentialGrowth (fun s => ∑ i, f i s) := by
  classical
  intro a b
  choose C K T hC hK hB using fun i => hf i a b
  let L := ∑ i, K i
  refine ⟨∑ i, C i, L, ∑ i, |T i|, Finset.sum_nonneg (fun i _ => hC i),
    Finset.sum_nonneg (fun i _ => hK i), fun s ha hb hs => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hTi : T i ≤ ∑ j, |T j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (T j)) hi)
  have hKi : K i ≤ L := Finset.single_le_sum (fun j _ => hK j) hi
  exact (hB i s ha hb (hTi.trans hs)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKi (abs_nonneg _))) (hC i))

private theorem pairFactor_cons (d : ComplexCharacterData) (ds es : List ComplexCharacterData) :
    complexPairLFactor (d :: ds) es = (complexPairLFactor [d] es).mul (complexPairLFactor es ds) := by
  rw [complexPairLFactor_comm es ds, complexPairLFactor, complexPairBlocks, List.flatMap_cons,
    complexLFactor_append]
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

private theorem pairFactor_singleton_ofFn {n : ℕ} (d : ComplexCharacterData)
    (e : Fin n → ComplexCharacterData) :
    complexPairLFactor [d] (List.ofFn e) = complexLFactor (List.ofFn fun j => d.mul (e j)) := by
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_ofFn]
  rfl

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 2) ℂ
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 2)
local notation "Mat" => Matrix (Fin (r + 2)) (Fin (r + 2)) ℂ

/-- The original equal-rank Jacquet expansion with actual square zeta factors and entire
adjacent-rank normalizations of exponential strip growth implies the equal-rank strip estimate. -/
def ComplexEqualJacquetStripGrowthStatement : Prop :=
  ∀ (k : ℕ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (es : Fin (r + 2) → ComplexCharacterData)
    (D : ComplexQuotientMeasureData (r + 1)) (W V : G → ℂ)
    (Φ : 𝓢(Fin (r + 2) → ℂ, ℂ))
    (D₁ : Fin k → ComplexQuotientMeasureData r) (U₁ : Fin k → H → ℂ) (V₁ : Fin k → G → ℂ)
    (μ : Fin k → Measure G) [∀ i, (μ i).IsHaarMeasure]
    (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (Φ₁ : Fin k → 𝓢(Mat, ℂ)) (f₁ : Fin k → G → ℂ),
    (∀ i, f₁ i ∈ complexStandardModule (r + 2) (List.ofFn fun j => d.mul (es j))) →
    (∀ i, ∃ R : OrdinaryIntegralNormalization
      (complexUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i))
      (fun s => ((complexPairLFactor (List.ofFn es) ds).denominator s)⁻¹),
      HasStripExponentialGrowth R.value) →
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → complexEqualIntegral D W V Φ s =
      ∑ i, complexUnequalIntegral (Nat.lt_succ_self r) (D₁ i) (V₁ i) (U₁ i) s *
        ∫ g, ComplexSquareZeta.zetaKernel (Φ₁ i) (f₁ i) s g ∂μ i) →
    ∃ R : OrdinaryIntegralNormalization (complexEqualIntegral D W V Φ)
      (fun s => ((complexPairLFactor (d :: ds) (List.ofFn es)).denominator s)⁻¹),
      HasStripExponentialGrowth R.value

theorem complexEqualJacquetStripGrowth : ComplexEqualJacquetStripGrowthStatement (r := r) := by
  intro k d ds es D W V Φ D₁ U₁ V₁ μ _ κ _ _ Φ₁ f₁ hf hA hExpansion
  obtain ⟨σ, hσ⟩ := hExpansion
  let La := complexPairLFactor (List.ofFn es) ds
  let Lz := complexPairLFactor [d] (List.ofFn es)
  let L := complexPairLFactor (d :: ds) (List.ofFn es)
  have hL : L = Lz.mul La := pairFactor_cons d ds (List.ofFn es)
  choose A hAg using hA
  choose a ha using fun i => (A i).eq_on_right
  choose b Z hZd hZg hZ using fun i => ComplexSquareZeta.complexSquareZetaStripGrowth (r := r + 1)
    (μ i) κ (fun j => d.mul (es j)) (Φ₁ i) (f₁ i) (hf i)
  obtain ⟨β, hβ⟩ := (Set.finite_range a).bddAbove
  obtain ⟨γ, hγ⟩ := (Set.finite_range b).bddAbove
  obtain ⟨τ, hτ⟩ := complexPairLFactor_denominator_ne_zero [d] (List.ofFn es)
  let N (s : ℂ) := ∑ i, (A i).value s * Z i s
  have hAd (i : Fin k) : Differentiable ℂ (A i).value :=
    fun s => ((A i).analytic s (mem_univ _)).differentiableAt
  have hNd : Differentiable ℂ N := Differentiable.fun_sum fun i _ =>
    (hAd i).mul (hZd i)
  have hNg : HasStripExponentialGrowth N := stripGrowth_sum (f := fun i s => (A i).value s * Z i s)
    fun i => (hAg i).mul (hZg i)
  refine ⟨⟨N, fun s _ => hNd.analyticAt s,
    ⟨max σ (max β (max γ τ)), fun s hs => ?_⟩⟩, hNg⟩
  have hs' := (le_max_right σ (max β (max γ τ))).trans_lt hs
  have hb' := (le_max_right β (max γ τ)).trans_lt hs'
  have hn := hτ s ((le_max_right γ τ).trans_lt hb')
  have hSquare (i : Fin k) :
      (∫ g, ComplexSquareZeta.zetaKernel (Φ₁ i) (f₁ i) s g ∂μ i) = Z i s * (Lz.denominator s)⁻¹ := by
    have hEq := (hZ i s ((hγ (Set.mem_range_self i)).trans_lt ((le_max_left γ τ).trans_lt hb'))).2
    rw [← pairFactor_singleton_ofFn d es] at hEq
    change Z i s = Lz.denominator s * _ at hEq
    rw [hEq, mul_comm (Lz.denominator s), mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [hσ s ((le_max_left _ _).trans_lt hs)]
  change _ = N s * (L.denominator s)⁻¹
  dsimp only [N]
  rw [hL, LocalFactor.ReciprocalEntire.denominator_mul, mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i s ((hβ (Set.mem_range_self i)).trans_lt ((le_max_left _ _).trans_lt hs')), hSquare i]
  ring

end Langlands.Global.RankinSelbergGlobal
