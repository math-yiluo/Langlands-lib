import Langlands.Analysis.SliceJetEstimates
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Tangential vector fields preserve flat jets on a slice -/

noncomputable section
set_option autoImplicit false

open scoped ContDiff

namespace Langlands.Analysis

universe uX uY uV

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem fderiv_directional_comm {f : X → V} (hf : ContDiff ℝ ∞ f)
    (x v w : X) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt.differentiableAt (by simp)
  have h (z : X) :
      fderiv ℝ (fun y => fderiv ℝ f y z) x = (fderiv ℝ (fderiv ℝ f) x).flip z := by
    rw [fderiv_clm_apply hd (differentiableAt_const z), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add]
  rw [h v, h w]
  exact (hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)) w v

/-- A constant real directional derivative commutes with evaluation of
every iterated derivative on a constant tuple of directions. -/
theorem iteratedFDeriv_directional_eq {f : X → V} (hf : ContDiff ℝ ∞ f) (v : X)
    (n : ℕ) (vs : Fin n → X) (x : X) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x vs =
      fderiv ℝ (fun y => iteratedFDeriv ℝ n f y vs) x v := by
  induction n generalizing x with
  | zero => simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
      have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ f y v) :=
        (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have h (y : X) :
          iteratedFDeriv ℝ n f y (Fin.tail vs) =
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) V (Fin.tail vs))
              (iteratedFDeriv ℝ n f y) := rfl
      have hn : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n f y (Fin.tail vs)) := by
        simp_rw [h]
        exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => X) V (Fin.tail vs)).contDiff.comp
          (hf.iteratedFDeriv_right (m := ∞) (by simp))
      have hd' : DifferentiableAt ℝ (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v)) x :=
        (hd.iteratedFDeriv_right (m := ∞) (by simp)).contDiffAt.differentiableAt (by simp)
      rw [hd'.iteratedFDeriv_succ_apply_left']
      simp_rw [ih (Fin.tail vs)]
      rw [fderiv_directional_comm hn]
      have he (y : X) :
          iteratedFDeriv ℝ (n + 1) f y vs =
            fderiv ℝ (fun z => iteratedFDeriv ℝ n f z (Fin.tail vs)) y (vs 0) := by
        have hf' : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
          (hf.iteratedFDeriv_right (m := ∞) (by simp)).contDiffAt.differentiableAt (by simp)
        exact hf'.iteratedFDeriv_succ_apply_left'
      simp_rw [he]

/-- The full jet of a function through order `m` vanishes everywhere
on the slice with second coordinate zero. -/
def IsFlatOnZeroSlice (m : ℕ) (f : X × Y → V) : Prop :=
  ∀ x : X, ∀ j ≤ m, iteratedFDeriv ℝ j f (x, (0 : Y)) = 0

/-- Multiplication by a smooth real scalar preserves zero jets. -/
theorem IsFlatOnZeroSlice.smul {m : ℕ} {f : X × Y → V} (hflat : IsFlatOnZeroSlice m f)
    (hf : ContDiff ℝ ∞ f) {a : X × Y → ℝ} (ha : ContDiff ℝ ∞ a) :
    IsFlatOnZeroSlice m (fun p => a p • f p) := by
  intro x j hj
  apply norm_le_zero_iff.mp
  refine (norm_iteratedFDeriv_smul_le ha hf (x, 0) (by simp)).trans_eq ?_
  exact Finset.sum_eq_zero fun i _ => by
    rw [hflat x (j - i) (le_trans (Nat.sub_le ..) hj), norm_zero, mul_zero]

/-- Differentiating by a smooth vector field tangent to the zero
slice preserves all orders of vanishing jets on the slice. -/
theorem IsFlatOnZeroSlice.tangential {m : ℕ} {f : X × Y → V}
    (hflat : IsFlatOnZeroSlice m f) (hf : ContDiff ℝ ∞ f)
    {W : X × Y → X × Y} (hW : ContDiff ℝ ∞ W) (hWt : ∀ x : X, (W (x, 0)).2 = 0) :
    IsFlatOnZeroSlice m (fun p => fderiv ℝ f p (W p)) := by
  intro x j hj
  let p : X × Y := (x, 0)
  let v : X × Y := W p
  let W₀ (q : X × Y) : X × Y := W q - v
  let f₀ (q : X × Y) : V := fderiv ℝ f q v
  let f₁ (q : X × Y) : V := fderiv ℝ f q (W₀ q)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hW₀ : ContDiff ℝ ∞ W₀ := hW.sub contDiff_const
  have hf₀ : ContDiff ℝ ∞ f₀ := hdf.clm_apply contDiff_const
  have hf₁ : ContDiff ℝ ∞ f₁ := hdf.clm_apply hW₀
  have hsum : (fun q => fderiv ℝ f q (W q)) = f₀ + f₁ := by
    funext q
    change fderiv ℝ f q (W q) = fderiv ℝ f q v + fderiv ℝ f q (W q - v)
    rw [← map_add, add_comm v, sub_add_cancel]
  have h₀ : iteratedFDeriv ℝ j f₀ p = 0 := by
    ext vs
    rw [zero_apply]
    change iteratedFDeriv ℝ j (fun q => fderiv ℝ f q v) p vs = 0
    rw [iteratedFDeriv_directional_eq hf]
    let H (q : X × Y) : V := iteratedFDeriv ℝ j f q vs
    let L : X →L[ℝ] X × Y := (ContinuousLinearMap.id ℝ X).prod 0
    have hH : ContDiff ℝ ∞ H :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => X × Y) V vs).contDiff.comp
        (hf.iteratedFDeriv_right (m := ∞) (by simp))
    have hzero : H ∘ L = fun _ => 0 := by
      funext z
      change iteratedFDeriv ℝ j f (z, 0) vs = 0
      rw [hflat z j hj, zero_apply]
    have hD := (((hH.contDiffAt (x := p)).differentiableAt (by simp)).hasFDerivAt.comp
      x L.hasFDerivAt).fderiv
    change fderiv ℝ (H ∘ L) x = (fderiv ℝ H p).comp L at hD
    rw [hzero, fderiv_const_apply] at hD
    have hv : L v.1 = v := Prod.ext rfl (hWt x).symm
    have h := DFunLike.congr_fun hD v.1
    change (0 : V) = fderiv ℝ H p (L v.1) at h
    simpa only [hv] using h.symm
  have h₁ : iteratedFDeriv ℝ j f₁ p = 0 := by
    apply norm_le_zero_iff.mp
    refine (norm_iteratedFDeriv_clm_apply hdf hW₀ p (by simp)).trans_eq ?_
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases he : i = j
    · subst i
      have hz : W₀ p = 0 := sub_self _
      rw [Nat.sub_self, iteratedFDeriv_zero_eq_comp, Function.comp_apply, hz,
        map_zero, norm_zero, mul_zero]
    · have hi' : i + 1 ≤ m := by omega
      rw [norm_iteratedFDeriv_fderiv, hflat x (i + 1) hi', norm_zero, mul_zero, zero_mul]
  rw [hsum, iteratedFDeriv_add_apply (hf₀.contDiffAt.of_le (by simp))
    (hf₁.contDiffAt.of_le (by simp)), h₀, h₁, add_zero]

end Langlands.Analysis
