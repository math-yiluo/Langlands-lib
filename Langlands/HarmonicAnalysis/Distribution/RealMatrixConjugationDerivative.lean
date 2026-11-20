import Langlands.HarmonicAnalysis.Distribution.RealMatrixTransposeOdd
import Langlands.HarmonicAnalysis.Distribution.SmoothTestParameters
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Infinitesimal conjugation invariance of smooth matrix distributions -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

section TimeDerivative

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : Compacts E} {s : Opens ℝ} {h : ℝ × E → F}
  (hh : ContDiff ℝ ∞ h) (h0 : (0 : ℝ) ∈ s)
  (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0)

include hh h0 hs in
private theorem smoothTimeDifferenceQuotient_support :
    ∀ t ∈ s, ∀ x ∉ K, smoothTimeDifferenceQuotient h (t, x) = 0 := by
  intro t ht x hx
  by_cases hn : t = 0
  · subst t
    have he : (fun r : ℝ => h (r, x)) =ᶠ[𝓝 0] (fun _ => (0 : F)) := by
      filter_upwards [s.isOpen.mem_nhds h0] with r hr
      exact hs r hr x hx
    have hc : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
    have hd := ((hh.differentiable (by simp) (0, x)).hasFDerivAt.comp_hasDerivAt 0 hc).deriv
    rw [smoothTimeDifferenceQuotient_zero, ← hd]
    rw [show (h ∘ fun r : ℝ => (r, x)) = (fun r => h (r, x)) from rfl, he.deriv_eq]
    simp
  · have hz := smul_smoothTimeDifferenceQuotient hh t x
    rw [hs t ht x hx, hs 0 h0 x hx, sub_zero] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn

/-- The time derivative at zero of a jointly smooth test family with a common
compact support. -/
def compactTestTimeDerivative : 𝓓_{K}(E, F) :=
  compactTestFamily (contDiff_smoothTimeDifferenceQuotient hh)
    (smoothTimeDifferenceQuotient_support hh h0 hs) ⟨0, h0⟩

@[simp]
theorem compactTestTimeDerivative_apply (x : E) :
    compactTestTimeDerivative hh h0 hs x = fderiv ℝ h (0, x) (1, 0) := by
  change smoothTimeDifferenceQuotient h (0, x) = _
  exact smoothTimeDifferenceQuotient_zero h x

/-- A continuous functional constant on the slices annihilates their time
derivative. -/
theorem eval_compactTestTimeDerivative_of_constant (T : 𝓓_{K}(E, F) →L[ℝ] G)
    (hT : ∀ t : s, T (compactTestFamily hh hs t) = T (compactTestFamily hh hs ⟨0, h0⟩)) :
    T (compactTestTimeDerivative hh h0 hs) = 0 := by
  let Q := compactTestFamily (contDiff_smoothTimeDifferenceQuotient hh)
    (smoothTimeDifferenceQuotient_support hh h0 hs)
  have hQ : Continuous Q := continuous_compactTestFamily _ _
  have hz (t : s) (ht : (t : ℝ) ≠ 0) : T (Q t) = 0 := by
    have heq : (t : ℝ) • Q t = compactTestFamily hh hs t - compactTestFamily hh hs ⟨0, h0⟩ := by
      ext x
      exact smul_smoothTimeDifferenceQuotient hh t.val x
    have h := congrArg T heq
    rw [map_smul, map_sub, hT t, sub_self] at h
    exact (smul_eq_zero.mp h).resolve_left ht
  have hclosed : IsClosed {t : s | T (Q t) = 0} :=
    isClosed_eq (T.continuous.comp hQ) continuous_const
  have hdense : Dense ((Subtype.val : s → ℝ) ⁻¹' ({0} : Set ℝ)ᶜ) :=
    (dense_compl_singleton 0).preimage s.isOpen.isOpenMap_subtype_val
  exact (closure_minimal (fun t ht => hz t (mem_compl_singleton_iff.mp ht)) hclosed)
    (hdense ⟨0, h0⟩)

end TimeDerivative

namespace RealGeneralLinearDistribution

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "GL" => Langlands.GeneralLinear n ℝ

private def expConjugatingUnit (X : Mat) (t : ℝ) : GL where
  val := NormedSpace.exp (t • X)
  inv := NormedSpace.exp (t • (-X))
  val_inv := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]

private def exponentialConjugation (X : Mat) (q : ℝ × Mat) : Mat :=
  NormedSpace.exp (q.1 • X) * q.2 * NormedSpace.exp (q.1 • (-X))

private theorem exponentialConjugation_zero (X A : Mat) : exponentialConjugation X (0, A) = A := by
  simp [exponentialConjugation]

private theorem exponentialConjugation_inverse (X A : Mat) (t : ℝ) :
    exponentialConjugation X (-t, exponentialConjugation X (t, A)) = A := by
  let u := expConjugatingUnit X t
  have hleft : NormedSpace.exp ((-t) • X) = ((u⁻¹ : GL) : Mat) := by
    change _ = NormedSpace.exp (t • (-X))
    rw [neg_smul, smul_neg]
  have hright : NormedSpace.exp ((-t) • (-X)) = (u : Mat) := by
    change _ = NormedSpace.exp (t • X)
    rw [neg_smul, smul_neg, neg_neg]
  change NormedSpace.exp ((-t) • X) * ((u : Mat) * A * ((u⁻¹ : GL) : Mat)) *
      NormedSpace.exp ((-t) • (-X)) = A
  rw [hleft, hright]
  calc
    _ = (((u⁻¹ : GL) : Mat) * u) * A * (((u⁻¹ : GL) : Mat) * u) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      have hu : ((u⁻¹ : GL) : Mat) * (u : Mat) = 1 := u.inv_val
      rw [hu, one_mul, mul_one]

private theorem contDiff_exponentialConjugation (X : Mat) :
    ContDiff ℝ ∞ (exponentialConjugation X) := by
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Mat → Mat) :=
    contDiff_iff_contDiffAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt
  exact ((hexp.comp (contDiff_fst.smul contDiff_const)).mul contDiff_snd).mul
    (hexp.comp (contDiff_fst.smul contDiff_const))

private def exponentialConjugationSupport (X : Mat) (f : FullTest n) : Compacts Mat :=
  ⟨exponentialConjugation X '' (Icc (-1 : ℝ) 1 ×ˢ tsupport f),
    (isCompact_Icc.prod f.hasCompactSupport).image (contDiff_exponentialConjugation X).continuous⟩

private def exponentialTimeDomain : Opens ℝ := ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩

private theorem exponentialConjugationTest_support (X : Mat) (f : FullTest n) :
    ∀ t ∈ exponentialTimeDomain, ∀ A ∉ exponentialConjugationSupport X f,
      f (exponentialConjugation X (t, A)) = 0 := by
  intro t ht A hA
  apply image_eq_zero_of_notMem_tsupport
  intro hB
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := ht
  exact hA ⟨(-t, exponentialConjugation X (t, A)), ⟨by
    exact ⟨by linarith [ht'.2], by linarith [ht'.1]⟩, hB⟩,
    exponentialConjugation_inverse X A t⟩

private theorem zero_mem_exponentialTimeDomain : (0 : ℝ) ∈ exponentialTimeDomain := by
  change (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
  norm_num

/-- The derivative of a full-space test along the exponential conjugation by `X`. -/
def fullConjugationDerivativeTest (X : Mat) (f : FullTest n) : FullTest n :=
  TestFunction.ofSupportedIn (subset_univ _) <|
    compactTestTimeDerivative (f.contDiff.comp (contDiff_exponentialConjugation X))
      zero_mem_exponentialTimeDomain (exponentialConjugationTest_support X f)

@[simp]
theorem fullConjugationDerivativeTest_apply (X : Mat) (f : FullTest n) (A : Mat) :
    fullConjugationDerivativeTest X f A = fderiv ℝ f A (X * A - A * X) := by
  rw [show fullConjugationDerivativeTest X f A =
      compactTestTimeDerivative (f.contDiff.comp (contDiff_exponentialConjugation X))
        zero_mem_exponentialTimeDomain (exponentialConjugationTest_support X f) A from rfl,
    compactTestTimeDerivative_apply]
  have htime : HasDerivAt (fun t : ℝ => (t, A)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 A)
  have hderiv := ((f.contDiff.comp (contDiff_exponentialConjugation X)).differentiable
    (by simp) (0, A)).hasFDerivAt.comp_hasDerivAt 0 htime
  have hconj : HasDerivAt (fun t : ℝ => exponentialConjugation X (t, A)) (X * A - A * X) 0 := by
    have h₁ := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).mul_const A
    have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
    simpa [exponentialConjugation, sub_eq_add_neg] using h₁.fun_mul h₂
  have hf : HasFDerivAt f (fderiv ℝ f A) (exponentialConjugation X (0, A)) := by
    rw [exponentialConjugation_zero]
    exact (f.contDiff.differentiable (by simp) A).hasFDerivAt
  exact hderiv.unique (hf.comp_hasDerivAt 0 hconj)

/-- A conjugation-invariant distribution annihilates the infinitesimal
conjugation derivatives of all full-space tests. -/
theorem eval_fullConjugationDerivativeTest_eq_zero (D : FullDistribution n)
    (hD : IsFullConjugationInvariant D) (X : Mat) (f : FullTest n) :
    D (fullConjugationDerivativeTest X f) = 0 := by
  let K := exponentialConjugationSupport X f
  let T : 𝓓_{K}(Mat, ℝ) →L[ℝ] ℂ := D.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))
  apply eval_compactTestTimeDerivative_of_constant
    (f.contDiff.comp (contDiff_exponentialConjugation X))
    zero_mem_exponentialTimeDomain (exponentialConjugationTest_support X f) T
  intro t
  have heq (r : exponentialTimeDomain) :
      (TestFunction.ofSupportedIn (subset_univ _) (compactTestFamily
        (f.contDiff.comp (contDiff_exponentialConjugation X))
        (exponentialConjugationTest_support X f) r) : FullTest n) =
      fullConjugationTest (expConjugatingUnit X r.val) f := by ext A; rfl
  change D (TestFunction.ofSupportedIn (subset_univ _) _) =
    D (TestFunction.ofSupportedIn (subset_univ _) _)
  rw [heq t, heq ⟨0, zero_mem_exponentialTimeDomain⟩, hD, hD]

end RealGeneralLinearDistribution

end Langlands.HarmonicAnalysis
