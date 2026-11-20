import Langlands.HarmonicAnalysis.Distribution.ProductTestJets
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Realizing a transverse derivative of one order on a product -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E W F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Opens E} {V : Opens W}

/-- A neighborhood of zero in a finite-dimensional real normed space admits a test
supported in the neighborhood and identically one near zero. -/
theorem exists_test_eq_one_near_zero [FiniteDimensional ℝ W] (hV : (0 : W) ∈ V) :
    ∃ χ : 𝓓(V, ℝ), (χ : W → ℝ) =ᶠ[𝓝 0] 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (V.isOpen.mem_nhds hV)
  let b : ContDiffBump (0 : W) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  exact ⟨⟨b, b.contDiff, b.hasCompactSupport, b.tsupport_eq ▸ hball⟩, b.eventuallyEq_one⟩

private def diagonalEvaluation (i : ℕ) (y : W) : (W [×i]→L[ℝ] F) →L[ℝ] F :=
  (ContinuousLinearMap.id ℝ (W [×i]→L[ℝ] F)).flipMultilinear (fun _ => y)

private theorem contDiff_diagonalEvaluation (i : ℕ) :
    ContDiff ℝ ∞ (diagonalEvaluation (W := W) (F := F) i) := by
  let e := (ContinuousLinearMap.id ℝ (W [×i]→L[ℝ] F)).flipMultilinear
  have hdiag : ContDiff ℝ ∞ (fun y : W => fun _ : Fin i => y) :=
    contDiff_pi.2 fun _ => contDiff_id
  exact (ContinuousMultilinearMap.contDiff (F := (W [×i]→L[ℝ] F) →L[ℝ] F) e).comp hdiag

private def productJetKernel (χ : 𝓓(V, ℝ)) (i : ℕ) : 𝓓(V, (W [×i]→L[ℝ] F) →L[ℝ] F) := by
  let c : W → ℝ := fun y => χ y * (i.factorial : ℝ)⁻¹
  let p := diagonalEvaluation (W := W) (F := F) i
  have hc : ContDiff ℝ ∞ c := χ.contDiff.mul (contDiff_const (c := (i.factorial : ℝ)⁻¹))
  have hs : tsupport (fun y => c y • p y) ⊆ tsupport χ :=
    (tsupport_smul_subset_left c p).trans tsupport_mul_subset_left
  have smoothSMul {B : Type _} [NormedAddCommGroup B] [NormedSpace ℝ B]
      {g : W → B} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun y => c y • g y) :=
    hc.smul hg
  exact ⟨fun y => c y • p y,
    smoothSMul (B := (W [×i]→L[ℝ] F) →L[ℝ] F) (contDiff_diagonalEvaluation i),
    χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans χ.tsupport_subset⟩

/-- Extend an order-`i` multilinear coefficient by its factorial-normalized
diagonal polynomial multiplied by a fixed cutoff on the second factor. -/
def productJetExtensionCLM (χ : 𝓓(V, ℝ)) (i : ℕ) :
    𝓓(U, W [×i]→L[ℝ] F) →L[ℝ] 𝓓(productTestDomain U V, F) :=
  productKernelTestCLM (productJetKernel χ i)

@[simp]
theorem productJetExtensionCLM_apply (χ : 𝓓(V, ℝ)) (i : ℕ)
    (a : 𝓓(U, W [×i]→L[ℝ] F)) (x : E) (y : W) :
    productJetExtensionCLM χ i a (x, y) =
      (χ y * (i.factorial : ℝ)⁻¹) • a x (fun _ => y) := rfl

theorem transverseProductJetCLM_apply_section (j : ℕ)
    (f : 𝓓(productTestDomain U V, F)) (x : E) (v : Fin j → W) :
    transverseProductJetCLM j f x v = iteratedFDeriv ℝ j (fun y => f (x, y)) 0 v := by
  let ι : W →L[ℝ] E × W := ContinuousLinearMap.inr ℝ E W
  let g : E × W → F := fun z => f ((x, 0) + z)
  have hg : ContDiff ℝ ∞ g := f.contDiff.comp (contDiff_const.add contDiff_id)
  have hf : (fun y => f (x, y)) = g ∘ ι := by
    funext y
    change f (x, y) = f (x + 0, 0 + y)
    simp
  have hι : ι 0 = 0 := map_zero ι
  rw [transverseProductJetCLM_apply, hf, ι.iteratedFDeriv_comp_right hg 0 (by simp), hι]
  change _ = iteratedFDeriv ℝ j (fun z : E × W => f ((x, 0) + z)) 0
    (fun k => (0, v k))
  rw [iteratedFDeriv_comp_add_left, add_zero]

private def diagonalSeries {i : ℕ} (a : W [×i]→L[ℝ] F) : FormalMultilinearSeries ℝ W F :=
  fun j => if h : i = j then h ▸ a else 0

private theorem iteratedFDeriv_diagonal_zero {i : ℕ} (a : W [×i]→L[ℝ] F)
    (j : ℕ) (v : Fin j → W) :
    iteratedFDeriv ℝ j (fun y => a (fun _ => y)) (0 : W) v =
      ∑ σ : Equiv.Perm (Fin j), diagonalSeries a j (v ∘ σ) := by
  let p := diagonalSeries a
  have hp : HasFiniteFPowerSeriesOnBall (fun y => a (fun _ => y)) p (0 : W) (i + 1) ⊤ := by
    refine HasFiniteFPowerSeriesOnBall.mk' ?_ ENNReal.zero_lt_top ?_
    · intro k hk
      exact dite_eq_right (Nat.ne_of_lt hk)
    · intro y _
      rw [Finset.sum_eq_single_of_mem i (Finset.self_mem_range_succ i), zero_add]
      · simp [p, diagonalSeries]
      · intro k _ hk
        simp [p, diagonalSeries, hk.symm]
  have ha : ContDiff ℝ ω (fun y => a (fun _ => y)) :=
    a.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  exact hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum ha.contDiffOn.analyticOn v

private theorem transverseProductJetCLM_productJetExtensionCLM_apply (χ : 𝓓(V, ℝ))
    (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1) (i j : ℕ)
    (a : 𝓓(U, W [×i]→L[ℝ] F)) (x : E) (v : Fin j → W) :
    transverseProductJetCLM j (productJetExtensionCLM χ i a) x v =
      ∑ σ : Equiv.Perm (Fin j), diagonalSeries ((i.factorial : ℝ)⁻¹ • a x) j (v ∘ σ) := by
  rw [transverseProductJetCLM_apply_section]
  have h : (fun y => productJetExtensionCLM χ i a (x, y)) =ᶠ[𝓝 (0 : W)]
      (fun y => ((i.factorial : ℝ)⁻¹ • a x) (fun _ => y)) := by
    filter_upwards [hχ] with y hy
    change χ y = 1 at hy
    simp [hy]
  rw [(h.iteratedFDeriv ℝ j).eq_of_nhds]
  exact iteratedFDeriv_diagonal_zero ((i.factorial : ℝ)⁻¹ • a x) j v

/-- Extending order `i` gives zero transverse derivative at any different order. -/
theorem transverseProductJetCLM_productJetExtensionCLM_of_ne (χ : 𝓓(V, ℝ))
    (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1) {i j : ℕ} (hij : i ≠ j)
    (a : 𝓓(U, W [×i]→L[ℝ] F)) :
    transverseProductJetCLM j (productJetExtensionCLM χ i a) = 0 := by
  ext x v
  rw [transverseProductJetCLM_productJetExtensionCLM_apply χ hχ]
  simp [diagonalSeries, hij]

/-- Extending order `i` and extracting the same order recovers every symmetric coefficient. -/
theorem transverseProductJetCLM_productJetExtensionCLM_self (χ : 𝓓(V, ℝ))
    (hχ : (χ : W → ℝ) =ᶠ[𝓝 0] 1) (i : ℕ)
    (a : 𝓓(U, W [×i]→L[ℝ] F))
    (ha : ∀ x v (σ : Equiv.Perm (Fin i)), a x (v ∘ σ) = a x v) :
    transverseProductJetCLM i (productJetExtensionCLM χ i a) = a := by
  ext x v
  rw [transverseProductJetCLM_productJetExtensionCLM_apply χ hχ]
  have hp : diagonalSeries ((i.factorial : ℝ)⁻¹ • a x) i = (i.factorial : ℝ)⁻¹ • a x := by
    unfold diagonalSeries
    rw [dite_eq_left rfl]
  simp only [hp, smul_apply, ha,
    Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero i

end Langlands.HarmonicAnalysis
