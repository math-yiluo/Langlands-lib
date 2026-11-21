import Langlands.Global.AdelicBlockParabolicPlaceNorm
import Langlands.Representation.Archimedean.BlockPrincipalSeriesNormalization
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Differential of the adelic parabolic half-modulus at one place -/

noncomputable section

open scoped BigOperators

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open NumberField Langlands.GeneralLinear Langlands.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

variable {n : ℕ} (B : BlockShape n)

/-- The trace of the diagonal block in an ambient matrix direction. -/
def blockTrace {R : Type*} [AddCommMonoid R] (X : Matrix (Fin n) (Fin n) R)
    (i : Fin B.length) : R :=
  ∑ a : Fin (B.size i), X (B.index i a) (B.index i a)

private theorem hasDerivAt_prod_at_one {ι A : Type*} [Fintype ι]
    [NormedCommRing A] [NormedAlgebra ℝ A] {f : ι → ℝ → A} {v : ι → A}
    (h0 : ∀ i, f i 0 = 1) (hf : ∀ i, HasDerivAt (f i) (v i) 0) :
    HasDerivAt (fun t => ∏ i, f i t) (∑ i, v i) 0 := by
  classical
  simpa only [h0, Finset.prod_const_one, one_smul] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) fun i _ => hf i)

private theorem exists_other_moved {d : ℕ} {σ : Equiv.Perm (Fin d)} (hσ : σ ≠ 1)
    (i : Fin d) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_cases hi : σ i = i
  · have hm : ∃ j, σ j ≠ j := by
      by_contra! h
      exact hσ (Equiv.ext h)
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, fun he => hj (he ▸ hi), hj⟩
  · exact ⟨σ i, hi, fun h => hi (σ.injective h)⟩

private theorem hasDerivAt_det_at_one {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    {d : ℕ} {p : ℝ → Matrix (Fin d) (Fin d) R} {X : Matrix (Fin d) (Fin d) R}
    (h0 : p 0 = 1) (hX : ∀ a b, HasDerivAt (fun t => p t a b) (X a b) 0) :
    HasDerivAt (fun t => (p t).det) X.trace 0 := by
  classical
  have hterm (σ : Equiv.Perm (Fin d)) :
      HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, p t (σ i) i)
        (if σ = 1 then X.trace else 0) 0 := by
    by_cases hσ : σ = 1
    · subst σ
      simpa [h0, Matrix.trace] using
        (hasDerivAt_prod_at_one (f := fun i t => p t i i)
          (fun i => by simp [h0]) (fun i => hX i i))
    · have hd := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin d)))
        (fun i _ => hX (σ i) i)
      have hz (i : Fin d) :
          (∏ j ∈ Finset.univ.erase i, p 0 (σ j) j) = 0 := by
        obtain ⟨j, hji, hj⟩ := exists_other_moved hσ i
        have hjmem : j ∈ Finset.univ.erase i := by simp [hji]
        exact Finset.prod_eq_zero hjmem (by simp [h0, hj])
      simp only [hz, zero_smul, Finset.sum_const_zero] at hd
      simpa [hσ] using hd.const_mul ((Equiv.Perm.sign σ : ℤ) : R)
  simpa only [← Matrix.det_apply', Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => hterm σ)

private theorem hasDerivAt_leviDet {R : Type*} [NormedCommRing R] [NormedAlgebra ℝ R]
    {p : ℝ → B.parabolic R} {X : Matrix (Fin n) (Fin n) R}
    (h0 : p 0 = 1) (hX : ∀ a b, HasDerivAt (fun t => (p t).val.val a b) (X a b) 0)
    (i : Fin B.length) :
    HasDerivAt (fun t => (B.leviProjection R (p t) i).val.det) (blockTrace B X i) 0 := by
  apply hasDerivAt_det_at_one (X := X.submatrix (B.index i) (B.index i))
  · simp [h0]
  · exact fun a b => hX (B.index i a) (B.index i b)

private theorem hasDerivAt_blockProduct {d : Fin B.length → ℝ → ℝ} {v : Fin B.length → ℝ}
    (h0 : ∀ i, d i 0 = 1) (hp : ∀ i t, 0 < d i t)
    (hd : ∀ i, HasDerivAt (d i) (v i) 0) :
    HasDerivAt (fun t => (Real.sqrt
      (∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        d i t ^ B.size j / d j t ^ B.size i) : ℂ))
      (↑(∑ i, blockHalfExponent B.size i * v i)) 0 := by
  simp_rw [sqrt_pairwiseBlockModulus B.size _ (fun i => hp i _)]
  apply HasDerivAt.ofReal_comp
  apply hasDerivAt_prod_at_one
  · simp [h0]
  · intro i
    simpa [h0, mul_comm] using
      (hd i).rpow_const (p := blockHalfExponent B.size i) (Or.inl (hp i 0).ne')

variable (F : Type u) [Field F] [NumberField F]

/-- At a real place the differential of the half-modulus is the weighted sum
of the diagonal-block traces. -/
theorem hasDerivAt_parabolicHalfCharacter_realPlace
    (v : {v : InfinitePlace F // v.IsReal}) {p : ℝ → B.parabolic ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (h0 : p 0 = 1)
    (hX : ∀ a b, HasDerivAt (fun t => (p t).val.val a b) (X a b) 0) :
    HasDerivAt (fun t =>
      (parabolicHalfCharacter F B (AdelicBlockParabolic.realPlaceInclusion F B v (p t)) : ℂ))
      (↑(∑ i, blockHalfExponent B.size i * blockTrace B X i)) 0 := by
  simp_rw [coe_parabolicHalfCharacter_realPlace, realPlaceModulusValue]
  apply hasDerivAt_blockProduct B
  · simp [h0]
  · intro i t
    exact abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)
  · intro i
    have h := hasDerivAt_leviDet B h0 hX i
    simpa using (h.hasFDerivAt.abs_of_pos (by simp [h0])).hasDerivAt

/-- At a complex place the normalized determinant uses the squared norm, so its
half-modulus differential uses twice the real part of each block trace. -/
theorem hasDerivAt_parabolicHalfCharacter_complexPlace
    (v : {v : InfinitePlace F // v.IsComplex}) {p : ℝ → B.parabolic ℂ}
    {X : Matrix (Fin n) (Fin n) ℂ} (h0 : p 0 = 1)
    (hX : ∀ a b, HasDerivAt (fun t => (p t).val.val a b) (X a b) 0) :
    HasDerivAt (fun t => (parabolicHalfCharacter F B
      (AdelicBlockParabolic.complexPlaceInclusion F B v (p t)) : ℂ))
      (↑(∑ i, blockHalfExponent B.size i * (2 * (blockTrace B X i).re))) 0 := by
  simp_rw [coe_parabolicHalfCharacter_complexPlace, complexPlaceModulusValue]
  apply hasDerivAt_blockProduct B
  · simp [h0]
  · intro i t
    exact pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)) _
  · intro i
    have h := (hasDerivAt_leviDet B h0 hX i).norm_sq
    simpa [h0, Complex.inner] using h

end Langlands.Global.AdelicBlockDeterminantCharacter
