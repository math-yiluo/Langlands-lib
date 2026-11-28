import Langlands.TraceFormula.SplitSmoothingPowers

/-! # Convolution powers of finite products of tests -/

noncomputable section

open MeasureTheory

namespace Langlands.TraceFormula

open Langlands.Hecke

universe u v w

variable {ι : Type u} [Fintype ι] {G : ι → Type v}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] [∀ i, T2Space (G i)]
  [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  (μ : (i : ι) → Measure (G i)) [∀ i, (μ i).IsHaarMeasure]

omit [∀ i, BorelSpace (G i)] [∀ i, T2Space (G i)] in
private theorem convolutionIntegral_piTensor (f g : (i : ι) → G i → ℂ) (x : ∀ i, G i) :
    convolutionIntegral (Measure.pi μ) (fun y => ∏ i, f i (y i))
        (fun y => ∏ i, g i (y i)) x =
      ∏ i, convolutionIntegral (μ i) (f i) (g i) (x i) := by
  simp only [convolutionIntegral, Pi.mul_apply, Pi.inv_apply, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i y => f i y * g i (y⁻¹ * x i))

variable {A : Type w} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  (m : Measure A) [m.IsHaarMeasure]
  (e : A ≃ₜ* (∀ i, G i)) (f : (i : ι) → G i → ℂ)

/-- With product Haar measure, a convolution power of a finite tensor is the tensor
of the local powers with the same exponent. -/
def FiniteProductSmoothingPowersStatement : Prop :=
  m.map e = Measure.pi μ →
  (∀ i, Continuous (f i)) → (∀ i, HasCompactSupport (f i)) →
  ∀ k : ℕ, positiveConvolutionPower m (fun x => ∏ i, f i (e x i)) k =
    fun x => ∏ i, positiveConvolutionPower (μ i) (f i) k (e x i)

theorem finiteProductSmoothingPowers : FiniteProductSmoothingPowersStatement μ m e f := by
  intro hm hf hs k
  let tensor : (∀ i, G i) → ℂ := fun x => ∏ i, f i (x i)
  have hTensorContinuous : Continuous tensor :=
    continuous_finsetProd _ fun i _ => (hf i).comp (continuous_apply i)
  have hTensorCompact : HasCompactSupport tensor := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi fun i => hs i)
    intro x hx
    exact Set.mem_univ_pi.mpr fun i => subset_tsupport _
      (fun hi => hx (Finset.prod_eq_zero (Finset.mem_univ i) hi))
  have hcont : Continuous (tensor ∘ e) := hTensorContinuous.comp e.continuous
  have hcompact : HasCompactSupport (tensor ∘ e) := hTensorCompact.comp_homeomorph e.toHomeomorph
  induction k with
  | zero => simp only [positiveConvolutionPower_zero]
  | succ k ih =>
      change positiveConvolutionPower m (tensor ∘ e) k =
        (fun y => ∏ i, positiveConvolutionPower (μ i) (f i) k (y i)) ∘ e at ih
      change positiveConvolutionPower m (tensor ∘ e) (k + 1) = _
      rw [positiveConvolutionPower_succ m hcont hcompact, ih]
      funext x
      rw [convolutionIntegral_comp_continuousMulEquiv e, hm, convolutionIntegral_piTensor]
      apply Finset.prod_congr rfl
      intro i _
      rw [positiveConvolutionPower_succ (μ i) (hf i) (hs i)]

end Langlands.TraceFormula
