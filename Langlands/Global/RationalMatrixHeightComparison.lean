import Langlands.Global.AdelicSiegelDiagonalHeightBound
import Langlands.Global.RationalFunctionHeight

/-! # Bounding the adelic matrix height by scalar entry heights -/

noncomputable section

universe u

open NumberField

namespace Langlands.Global.AdelicMatrixHeight

open Height MatrixInverseHeight

/-- Indices for the entries of a square matrix and its inverse. -/
abbrev MatrixAndInverseIndex (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

/-- Read an entry of an invertible matrix or its inverse. -/
def matrixAndInverseEntry {R : Type*} [CommRing R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) : MatrixAndInverseIndex n → R
  | .inl (i, j) => g i j
  | .inr (i, j) => g⁻¹ i j

private theorem localMaximum_le_entry_product {R K : Type*} [CommRing R] [NormedField K]
    (f : R →+* K) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    localMaximum f g ≤ ∏ a : MatrixAndInverseIndex n, max ‖f (matrixAndInverseEntry g a)‖ 1 := by
  let factor (a : MatrixAndInverseIndex n) : ℝ := max ‖f (matrixAndInverseEntry g a)‖ 1
  have hfactor (a : MatrixAndInverseIndex n) : 1 ≤ factor a := le_max_right _ _
  have hprod : 0 ≤ ∏ a, factor a := Finset.prod_nonneg fun a _ => zero_le_one.trans (hfactor a)
  have hentry (a : MatrixAndInverseIndex n) :
      ‖f (matrixAndInverseEntry g a)‖ ≤ ∏ b, factor b :=
    (le_max_left _ _).trans <| by
      simpa only [max_eq_left (hfactor _)] using Finset.le_prod_max_one (Finset.mem_univ a) factor
  apply max_le
  · exact (pi_norm_le_iff_of_nonneg hprod).mpr fun i =>
      (pi_norm_le_iff_of_nonneg hprod).mpr fun j => hentry (.inl (i, j))
  · exact (pi_norm_le_iff_of_nonneg hprod).mpr fun i =>
      (pi_norm_le_iff_of_nonneg hprod).mpr fun j => hentry (.inr (i, j))

variable (F : Type u) [Field F] [NumberField F]

private theorem hasFiniteMulSupport_max_finitePlace (a : F) :
    (fun v : NumberField.FinitePlace F => max (v a) 1).HasFiniteMulSupport := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [Function.HasFiniteMulSupport]
  · exact (NumberField.FinitePlace.hasFiniteMulSupport ha).fun_comp
      (g := fun r : ℝ => max r 1) (max_self 1)

/-- The matrix-and-inverse height of a diagonal rational matrix is bounded by
the product of its scalar entry heights times the archimedean dimension factor. -/
theorem rational_height_le_entry_product {n : ℕ} (hn : 0 < n) (g : RationalGL F n) :
    height F n (AdelicGL.rational F n g) ≤
      (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) *
        ∏ a : MatrixAndInverseIndex n, mulHeight₁ (matrixAndInverseEntry g a) := by
  classical
  let e := (NumberField.FinitePlace.equivHeightOneSpectrum (K := F)).symm
  let arch (v : InfinitePlace F) (a : MatrixAndInverseIndex n) : ℝ :=
    max (v (matrixAndInverseEntry g a)) 1 ^ v.mult
  let finite (v : NumberField.FinitePlace F) (a : MatrixAndInverseIndex n) : ℝ :=
    max (v (matrixAndInverseEntry g a)) 1
  have hentry (a : MatrixAndInverseIndex n) :
      matrixAndInverseEntry (AdelicGL.rational F n g) a = diagonal F (matrixAndInverseEntry g a) := by
    rcases a with ⟨i, j⟩ | ⟨i, j⟩
    · exact AdelicGL.rational_apply F n g i j
    · change ((AdelicGL.rational F n g)⁻¹) i j = diagonal F (g⁻¹ i j)
      rw [← map_inv]
      exact AdelicGL.rational_apply F n g⁻¹ i j
  have harch (v : InfinitePlace F) :
      infiniteLocal F n (AdelicGL.rational F n g) v ^ v.mult ≤ ∏ a, arch v a := by
    dsimp only [arch]
    rw [Finset.prod_pow]
    apply pow_le_pow_left₀ (localMaximum_nonneg _ _) _ _
    simpa only [infiniteLocal, hentry, AdelicSiegelFactors.norm_infiniteProjection_diagonal]
      using localMaximum_le_entry_product (infiniteProjection F v) (AdelicGL.rational F n g)
  have hfinite (v : FinitePlace F) :
      finiteLocal F n (AdelicGL.rational F n g) v ≤ ∏ a, finite (e v) a := by
    simpa only [finiteLocal, hentry, AdelicSiegelFactors.norm_finiteProjection_diagonal]
      using localMaximum_le_entry_product (finiteProjection F v) (AdelicGL.rational F n g)
  have hsupport (a : MatrixAndInverseIndex n) :
      (fun v => finite v a).HasFiniteMulSupport :=
    hasFiniteMulSupport_max_finitePlace F (matrixAndInverseEntry g a)
  have hprodFinite :
      (∏ᶠ v, finiteLocal F n (AdelicGL.rational F n g) v) ≤ ∏ a, ∏ᶠ v, finite v a := by
    rw [← finprod_prod_comm Finset.univ finite (fun a _ => hsupport a), ← finprod_comp_equiv e]
    have hs : (fun v : NumberField.FinitePlace F => ∏ a, finite v a).HasFiniteMulSupport :=
      Function.HasFiniteMulSupport.prod hsupport Finset.univ
    exact finprod_le_finprod₀ (hasFiniteMulSupport_finiteLocal F n hn _)
      (fun _ => localMaximum_nonneg _ _)
      (hs.fun_comp_of_injective (g := e) e.injective) hfinite
  have hprodArch :
      (∏ v : InfinitePlace F, infiniteLocal F n (AdelicGL.rational F n g) v ^ v.mult) ≤
        ∏ a, ∏ v, arch v a := by
    rw [Finset.prod_comm]
    exact Finset.prod_le_prod₀ (fun v _ => pow_nonneg (localMaximum_nonneg _ _) _) (fun v _ => harch v)
  rw [height_eq_scalar_mul_sourceNorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [sourceNorm, NumberField.mulHeight₁_eq, Finset.prod_mul_distrib]
  exact mul_le_mul hprodArch hprodFinite (finprod_nonneg fun _ => localMaximum_nonneg _ _)
    (Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun v _ =>
      pow_nonneg (zero_le_one.trans (le_max_right _ _)) _)

/-- Polynomial bounds on the scalar heights of all matrix entries and inverse
entries give a polynomial bound on the normalized adelic matrix height. -/
theorem exists_rational_height_powerBound {X : Type*} {n : ℕ}
    (g : X → RationalGL F n) (H : X → ℝ) (hH : ∀ x, 1 ≤ H x)
    (hentry : ∀ a, (fun x => matrixAndInverseEntry (g x) a) ∈ polynomialHeightBounded H hH) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x, max 1 (height F n (AdelicGL.rational F n (g x))) ≤
      C * H x ^ d := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_lt_one, 0, fun x => ?_⟩
    have harch : (∏ v : InfinitePlace F, (0 : ℝ) ^ v.mult) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Classical.choice (inferInstance : Nonempty (InfinitePlace F))))
        (by simp [zero_pow, InfinitePlace.mult_ne_zero])
    simpa only [height, Nat.cast_zero, zero_mul, harch, max_eq_left zero_le_one, pow_zero, mul_one]
      using (le_refl (1 : ℝ))
  choose c hc d hd using hentry
  refine ⟨(n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * ∏ a, c a,
    mul_pos (pow_pos (Nat.cast_pos.mpr hn) _) (Finset.prod_pos fun a _ => hc a),
    ∑ a, d a, fun x => ?_⟩
  rw [max_eq_right (one_le_height F n hn _)]
  refine (rational_height_le_entry_product F hn (g x)).trans ?_
  calc
    _ ≤ (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult) * ∏ a, (c a * H x ^ d a) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => mulHeight₁_nonneg _)
        (fun a _ => hd a x)) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]

end Langlands.Global.AdelicMatrixHeight
