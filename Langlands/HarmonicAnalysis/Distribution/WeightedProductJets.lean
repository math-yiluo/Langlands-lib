import Langlands.HarmonicAnalysis.Distribution.ProductFiberIntegral
import Langlands.HarmonicAnalysis.Distribution.ProductJetExtension
import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Multiplication of leading jets and integration over an independent coordinate -/

noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

section LeadingProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the lower derivatives of the vector-valued factor vanish, multiplication
acts on its leading derivative by the value of the scalar multiplier. -/
theorem iteratedFDeriv_smul_of_lower_eq_zero {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    {a : E → ℝ} {g : E → F} (ha : ContDiffOn ℝ ∞ a s) (hg : ContDiffOn ℝ ∞ g s)
    (i : ℕ) (hzero : ∀ j < i, iteratedFDeriv ℝ j g x = 0) :
    iteratedFDeriv ℝ i (fun y => a y • g y) x = a x • iteratedFDeriv ℝ i g x := by
  let b : E → ℝ := fun y => a y - a x
  have hb : ContDiffOn ℝ ∞ b s := ha.sub contDiffOn_const
  have hi : (i : WithTop ℕ∞) ≤ ∞ := by simp
  have hn := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) hb hg hs.uniqueDiffOn hx hi
  have hsum :
      (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j b s x‖ *
        ‖iteratedFDerivWithin ℝ (i - j) g s x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hs hx, iteratedFDerivWithin_of_isOpen (i - j) hs hx]
    by_cases h : j = 0
    · subst j
      simp [b]
    · have hle : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hj' : i - j < i := by omega
      rw [hzero (i - j) hj', norm_zero, mul_zero]
  rw [iteratedFDerivWithin_of_isOpen i hs hx, hsum] at hn
  have hflat := norm_le_zero_iff.mp hn
  have hf : (fun y => b y • g y) = (fun y => a y • g y) - (fun y => a x • g y) := by
    funext y
    exact sub_smul _ _ _
  have ha' := ha.contDiffAt (hs.mem_nhds hx)
  have hg' := hg.contDiffAt (hs.mem_nhds hx)
  rw [hf, iteratedFDeriv_sub_apply (f := fun y => a y • g y) (g := fun y => a x • g y)
    ((ha'.smul hg').of_le hi) ((hg'.const_smul (a x)).of_le hi),
    iteratedFDeriv_const_smul_apply' (hg'.of_le hi)] at hflat
  exact sub_eq_zero.mp hflat

end LeadingProduct

section Pullback

variable {E W E' W' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U' : Opens E'} {V' : Opens W'}

/-- Leading transverse derivative of a weighted smooth pullback preserving the
zero section at the point of evaluation. -/
theorem weighted_transverseProductJet_comp_of_lower_eq_zero
    (f : 𝓓(productTestDomain U' V', F)) {s : Set (E × W)} (hs : IsOpen s)
    {a : E × W → ℝ} (ha : ContDiffOn ℝ ∞ a s)
    {H : E × W → E' × W'} (hH : ContDiffOn ℝ ∞ H s) {x : E} {x' : E'}
    (hx : (x, 0) ∈ s) (hH0 : H (x, 0) = (x', 0))
    (i : ℕ) (hzero : ∀ j < i, transverseProductJetCLM j f = 0) (v : Fin i → W) :
    iteratedFDeriv ℝ i (fun p => a p • f (H p)) (x, 0) (fun k => (0, v k)) =
      a (x, 0) • transverseProductJetCLM i f x'
        (fun k => productNormalDerivative H x (v k)) := by
  have hflat (j : ℕ) (hj : j < i) : iteratedFDeriv ℝ j f (H (x, 0)) = 0 := by
    rw [hH0]
    refine iteratedFDeriv_eq_zero_of_transverseJets f.contDiff j ?_ j le_rfl x'
    intro z k hk w
    rw [← transverseProductJetCLM_apply, hzero k (hk.trans_lt hj)]
    rfl
  have hcomp : ContDiffOn ℝ ∞ ((f : E' × W' → F) ∘ H) s :=
    f.contDiff.comp_contDiffOn hH
  have hlow (j : ℕ) (hj : j < i) : iteratedFDeriv ℝ j ((f : E' × W' → F) ∘ H) (x, 0) = 0 := by
    ext w
    rw [iteratedFDeriv_comp_of_lower_eq_zero f.contDiff.contDiffAt
      (hH.contDiffAt (hs.mem_nhds hx)) j (fun k hk => hflat k (hk.trans hj)),
      hflat j hj]
    rfl
  have he := iteratedFDeriv_smul_of_lower_eq_zero hs hx ha hcomp i hlow
  change iteratedFDeriv ℝ i (fun p => a p • ((f : E' × W' → F) ∘ H) p) (x, 0)
    (fun k => (0, v k)) = _
  rw [he, smul_apply, transverseProductJet_comp_of_lower_eq_zero f
    (hH.contDiffAt (hs.mem_nhds hx)) hH0 i hzero]

end Pullback

section Integral

variable {E W T F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [MeasurableSpace T] [BorelSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens W} {Q : Opens T}
  (μ : Measure T) [IsLocallyFiniteMeasure μ]

/-- The transverse jet of an integral over an independent product coordinate. -/
def productFiberNormalJet (i : ℕ)
    (f : 𝓓(productTestDomain (productTestDomain U V) Q, F)) :
    𝓓(U, W [×i]→L[ℝ] F) :=
  transverseProductJetCLM i (productFiberIntegralTest μ f)

theorem productFiberNormalJet_apply (i : ℕ)
    (f : 𝓓(productTestDomain (productTestDomain U V) Q, F)) (x : E) (v : Fin i → W) :
    productFiberNormalJet μ i f x v =
      ∫ t, iteratedFDeriv ℝ i (fun p : E × W => f (p, t)) (x, 0)
        (fun k => (0, v k)) ∂μ := by
  unfold productFiberNormalJet
  rw [transverseProductJetCLM_apply, iteratedFDeriv_productFiberIntegralTest_apply]

end Integral

end Langlands.HarmonicAnalysis
