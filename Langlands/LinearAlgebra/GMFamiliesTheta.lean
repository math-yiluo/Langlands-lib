import Langlands.LinearAlgebra.GMFamilies
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Alternating identities for the theta factors -/

noncomputable section

open scoped RealInnerProductSpace Matrix
open Classical Matrix

namespace Langlands.GMFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The family dual to an independent family in its Euclidean span. -/
def gramDual (v : ι → E) (i : ι) : E :=
  ∑ j, (Matrix.gram ℝ v)⁻¹ i j • v j

theorem gramDual_mem_span (v : ι → E) (i : ι) :
    gramDual v i ∈ Submodule.span ℝ (Set.range v) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

private theorem det_gram_pos (v : ι → E) (hv : LinearIndependent ℝ v) :
    0 < (Matrix.gram ℝ v).det := (Matrix.posDef_gram_iff_linearIndependent.mpr hv).det_pos

/-- The Gram dual has Kronecker inner products with the given vectors. -/
theorem inner_gramDual (v : ι → E) (hv : LinearIndependent ℝ v) (i j : ι) :
    ⟪gramDual v i, v j⟫ = (1 : Matrix ι ι ℝ) i j := by
  have h := (Matrix.gram ℝ v).nonsing_inv_mul (isUnit_iff_ne_zero.mpr (det_gram_pos v hv).ne')
  simpa only [gramDual, sum_inner, real_inner_smul_left, Matrix.mul_apply, Matrix.gram_apply]
    using congrArg (fun M : Matrix ι ι ℝ => M i j) h

theorem inner_gramDual_self (v : ι → E) (hv : LinearIndependent ℝ v) (i : ι) :
    ⟪gramDual v i, v i⟫ = 1 := by rw [inner_gramDual v hv, Matrix.one_apply_eq]

theorem inner_gramDual_ne (v : ι → E) (hv : LinearIndependent ℝ v) {i j : ι} (h : i ≠ j) :
    ⟪gramDual v i, v j⟫ = 0 := by rw [inner_gramDual v hv, Matrix.one_apply_ne h]

theorem gramDual_ne_zero (v : ι → E) (hv : LinearIndependent ℝ v) (i : ι) : gramDual v i ≠ 0 := by
  intro hi
  simpa [hi] using inner_gramDual v hv i i

theorem eq_gramDual_of_inner (v : ι → E) (hv : LinearIndependent ℝ v) (i : ι) (w : E)
    (hw : w ∈ Submodule.span ℝ (Set.range v))
    (h : ∀ j, ⟪w, v j⟫ = (1 : Matrix ι ι ℝ) i j) : w = gramDual v i := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have hz : Submodule.span ℝ (Set.range v) ≤ ((innerₗ E) (w - gramDual v i)).ker := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp [h j, inner_gramDual v hv]
  exact hz (Submodule.sub_mem _ hw (gramDual_mem_span v i))

theorem eq_gramDual_of_pairings (v : ι → E) (hv : LinearIndependent ℝ v) (i : ι) (w : E)
    (hw : w ∈ Submodule.span ℝ (Set.range v)) (hi : ⟪w, v i⟫ = 1)
    (h : ∀ j, i ≠ j → ⟪w, v j⟫ = 0) : w = gramDual v i := by
  apply eq_gramDual_of_inner v hv i w hw
  intro j
  by_cases hij : i = j
  · subst j
    simpa using hi
  · rw [Matrix.one_apply_ne hij]
    exact h j hij

/-- The Gram dual is unchanged as a family by consistent reindexing. -/
theorem gramDual_reindex {κ : Type*} [Fintype κ] (e : κ ≃ ι) (v : ι → E)
    (hv : LinearIndependent ℝ v) (i : κ) : gramDual (fun j => v (e j)) i = gramDual v (e i) := by
  symm
  apply eq_gramDual_of_inner _ (hv.comp e e.injective)
  · refine Submodule.span_mono ?_ (gramDual_mem_span v (e i))
    rintro _ ⟨j, rfl⟩
    exact ⟨e.symm j, by simp⟩
  · intro j
    simp [inner_gramDual v hv, Matrix.one_apply]

private theorem eq_sum_smul_gramDual (v : ι → E) (hv : LinearIndependent ℝ v) (i : ι) :
    v i = ∑ j, Matrix.gram ℝ v i j • gramDual v j := by
  have h := (Matrix.gram ℝ v).mul_nonsing_inv (isUnit_iff_ne_zero.mpr (det_gram_pos v hv).ne')
  simp only [gramDual, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

private theorem gramVolume_eq_sqrt (v : ι → E) [DecidableEq ι] :
    gramVolume v = Real.sqrt (Matrix.gram ℝ v).det := by
  unfold gramVolume
  congr 2

/-- Reindexing a Euclidean family preserves its theta factor. -/
theorem thetaOf_reindex (a : Submodule ℝ E) {κ : Type*} [Fintype κ] (e : κ ≃ ι)
    (v : ι → a) (Λ : StrongDual ℝ a) : thetaOf a (fun i => v (e i)) Λ = thetaOf a v Λ := by
  have he := Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ fun i => (v i : E))
  simp only [thetaOf, gramVolume]
  congr 1
  · exact congrArg (fun r : ℝ => ((Real.sqrt r : ℝ) : ℂ)⁻¹) he
  · exact e.prod_comp (fun i => Complex.I * (Λ (v i) : ℂ))

theorem thetaOf_inv (a : Submodule ℝ E) (v : ι → a) (Λ : StrongDual ℝ a) :
    (thetaOf a v Λ)⁻¹ = ((gramVolume (fun i => (v i : E)) : ℝ) : ℂ) *
      ∏ i, (Complex.I * (Λ (v i) : ℂ))⁻¹ := by
  rw [thetaOf, mul_inv, inv_inv, Finset.prod_inv_distrib]

@[simp] theorem thetaOf_isEmpty (a : Submodule ℝ E) [IsEmpty ι] (v : ι → a) (Λ : StrongDual ℝ a) :
    thetaOf a v Λ = 1 := by simp [thetaOf, gramVolume]

/-- The hatted theta factor is the theta factor of a Gram dual family. -/
theorem thetaHat_eq_thetaOf_gramDual [FiniteDimensional ℝ E] (a : Submodule ℝ E) (S : Finset E) (Λ : StrongDual ℝ a) :
    thetaHat S Λ = thetaOf a (gramDual fun i : simpleRoots a S => (i : a)) Λ := by
  have hv (i : simpleRoots a S) : coweight (simpleRoots a S) i = gramDual (fun j : simpleRoots a S => (j : a)) i := by
    unfold coweight gramDual
    have hg : gram (simpleRoots a S) = Matrix.gram ℝ (fun j : simpleRoots a S => (j : a)) := rfl
    rw [hg]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply congrArg (fun M : Matrix (simpleRoots a S) (simpleRoots a S) ℝ => M i j)
    exact congrArg (fun d : DecidableEq (simpleRoots a S) =>
      @Inv.inv _ (@Matrix.inv _ _ _ d _) (Matrix.gram ℝ (fun j : simpleRoots a S => (j : a))))
      (Subsingleton.elim _ _)
  simp only [thetaHat, thetaOf, hv]

private def rowPiecewise {K : Type*} (J : Finset ι) (A B : Matrix ι ι K) : Matrix ι ι K :=
  Matrix.of fun i j => if i ∈ J then A i j else B i j

omit [Fintype ι] in
private theorem rowPiecewise_apply {K : Type*} (J : Finset ι) (A B : Matrix ι ι K) (i j : ι) :
    rowPiecewise J A B i j = if i ∈ J then A i j else B i j := rfl

private theorem det_same_matrix {κ K : Type*} [CommRing K] (M : Matrix κ κ K)
    (d₁ d₂ : DecidableEq κ) (e₁ e₂ : Fintype κ) :
    @Matrix.det κ d₁ e₁ K _ M = @Matrix.det κ d₂ e₂ K _ M := by
  rw [Subsingleton.elim d₁ d₂, Subsingleton.elim e₁ e₂]

private theorem det_two_blocks {K : Type*} [CommRing K] (M : Matrix ι ι K) (J : Finset ι)
    (hz : ∀ i ∉ J, ∀ j ∈ J, M i j = 0) :
    M.det = (M.submatrix (Subtype.val : J → ι) Subtype.val).det *
      (M.submatrix (Subtype.val : {i // i ∉ J} → ι) Subtype.val).det := by
  rw [M.twoBlockTriangular_det (· ∈ J) hz]
  exact congrArg₂ (· * ·) (det_same_matrix _ _ _ _ _) (det_same_matrix _ _ _ _ _)

section MixedGram

variable (v : ι → E)

private theorem gram_linearCombination (C : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun i => ∑ j, C i j • v j) = C * Matrix.gram ℝ v * C.transpose := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

set_option maxHeartbeats 600000 in
/-- The product of the volumes on complementary subsets of a family and its Gram dual,
multiplied by the full volume, is the principal Gram determinant. -/
private theorem gramVolume_mul_mixed (hv : LinearIndependent ℝ v) (J : Finset ι) :
    gramVolume (fun i : J => v i) * gramVolume (fun i : {i // i ∉ J} => gramDual v i) * gramVolume v =
      (Matrix.gram ℝ (fun i : J => v i)).det := by
  let G := Matrix.gram ℝ v
  let C := rowPiecewise J 1 G⁻¹
  let m := J.piecewise v (gramDual v)
  let GJ := Matrix.gram ℝ (fun i : J => v i)
  let HJ := Matrix.gram ℝ (fun i : {i // i ∉ J} => gramDual v i)
  have hun : IsUnit G.det := isUnit_iff_ne_zero.mpr (det_gram_pos v hv).ne'
  have hm : m = fun i => ∑ j, C i j • v j := by
    funext i
    by_cases hi : i ∈ J
    · simp only [m, Finset.piecewise, hi, ite_true, C, rowPiecewise_apply, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [m, Finset.piecewise, hi, ite_false, C, rowPiecewise_apply, G, gramDual]
  have hpair : C * G = rowPiecewise J G 1 := by
    ext i j
    by_cases hi : i ∈ J
    · simp only [Matrix.mul_apply, C, rowPiecewise_apply, hi, ite_true,
        Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
    · rw [Matrix.mul_apply]
      simp only [C, rowPiecewise_apply, hi, ite_false]
      rw [← Matrix.mul_apply, G.nonsing_inv_mul hun]
  have hd : (C * G).det = GJ.det := by
    rw [hpair, det_two_blocks _ J]
    · have h₁ : (rowPiecewise J G 1).submatrix (Subtype.val : J → ι) Subtype.val = GJ := by
        ext i j
        change rowPiecewise J G 1 i.1 j.1 = _
        rw [rowPiecewise_apply, ite_eq_left i.property]
        rfl
      have h₂ : (rowPiecewise J G 1).submatrix (Subtype.val : {i // i ∉ J} → ι)
          (Subtype.val : {i // i ∉ J} → ι) = 1 := by
        ext i j
        change rowPiecewise J G 1 i.1 j.1 = _
        simp only [rowPiecewise_apply, i.property, ite_false, Matrix.one_apply, Subtype.ext_iff]
      rw [h₁, h₂, Matrix.det_one, mul_one]
    · intro i hi j hj
      have hne : i ≠ j := fun he => hi (he ▸ hj)
      simp only [rowPiecewise_apply, hi, ite_false, Matrix.one_apply, hne]
  have hmix : (Matrix.gram ℝ m).det = GJ.det * HJ.det := by
    rw [det_two_blocks _ J]
    · have h₁ : (Matrix.gram ℝ m).submatrix (Subtype.val : J → ι) Subtype.val = GJ := by
        ext i j
        change ⟪m i.1, m j.1⟫ = ⟪v i.1, v j.1⟫
        simp only [m, Finset.piecewise, i.property, j.property, ite_true]
      have h₂ : (Matrix.gram ℝ m).submatrix (Subtype.val : {i // i ∉ J} → ι) Subtype.val = HJ := by
        ext i j
        change ⟪m i.1, m j.1⟫ = ⟪gramDual v i.1, gramDual v j.1⟫
        simp only [m, Finset.piecewise, i.property, j.property, ite_false]
      rw [h₁, h₂]
    · intro i hi j hj
      simp only [m, Matrix.gram_apply, Finset.piecewise, hi, hj, ite_true, ite_false, inner_gramDual v hv]
      exact Matrix.one_apply_ne (fun he => hi (he ▸ hj))
  have hsq : (Matrix.gram ℝ m).det * G.det = GJ.det ^ 2 := by
    rw [hm, gram_linearCombination, Matrix.det_mul, Matrix.det_transpose, ← hd, Matrix.det_mul]
    ring
  rw [gramVolume_eq_sqrt, gramVolume_eq_sqrt, gramVolume_eq_sqrt]
  change Real.sqrt GJ.det * Real.sqrt HJ.det * Real.sqrt G.det = GJ.det
  rw [← Real.sqrt_mul' _ (Matrix.posSemidef_gram ℝ _).det_nonneg, ← hmix,
    ← Real.sqrt_mul' _ (det_gram_pos v hv).le, hsq,
    Real.sqrt_sq (Matrix.posSemidef_gram ℝ _).det_nonneg]

end MixedGram

private theorem det_add_eq_sum_rowPiecewise (A B : Matrix ι ι ℂ) :
    (A + B).det = ∑ J : Finset ι, (rowPiecewise J A B).det := by
  have h := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).map_add_univ
    (fun i => A i) (fun i => B i)
  change (A + B).det = ∑ J : Finset ι, (Matrix.of (J.piecewise (fun i => A i) (fun i => B i))).det at h
  rw [h]
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  ext i j
  simp only [Finset.piecewise, rowPiecewise_apply, Matrix.of_apply]
  split <;> rfl

private theorem det_rowPiecewise_diagonal (G : Matrix ι ι ℂ) (x y : ι → ℂ) (J : Finset ι) :
    (rowPiecewise J (diagonal x * G) (diagonal y)).det =
      (G.submatrix (Subtype.val : J → ι) Subtype.val).det * (∏ i : J, x i) *
        ∏ i : {i // i ∉ J}, y i := by
  let M := rowPiecewise J (diagonal x * G) (diagonal y)
  have hz (i : ι) (hi : i ∉ J) (j : ι) (hj : j ∈ J) : M i j = 0 := by
    have hne : i ≠ j := fun he => hi (he ▸ hj)
    simp only [M, rowPiecewise_apply, hi, ite_false, diagonal_apply, hne]
  have h₁ : M.submatrix (Subtype.val : J → ι) (Subtype.val : J → ι) =
      diagonal (fun i : J => x i) * G.submatrix (Subtype.val : J → ι) (Subtype.val : J → ι) := by
    ext i j
    change rowPiecewise J (diagonal x * G) (diagonal y) i.1 j.1 = _
    simp only [rowPiecewise_apply, i.property, ite_true, Matrix.diagonal_mul, Matrix.submatrix_apply]
  have h₂ : M.submatrix (Subtype.val : {i // i ∉ J} → ι) Subtype.val = diagonal (fun i : {i // i ∉ J} => y i) := by
    ext i j
    change rowPiecewise J (diagonal x * G) (diagonal y) i.1 j.1 = _
    simp only [rowPiecewise_apply, i.property, ite_false, diagonal_apply, Subtype.ext_iff]
  change M.det = _
  rw [det_two_blocks M J hz, h₁, h₂, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, mul_comm (∏ i : J, x i)]

set_option maxHeartbeats 600000 in
/-- Alternating inverse-theta cancellation for a nonempty independent family and its Gram dual. -/
theorem alternating_thetaOf_inv [Nonempty ι] (a : Submodule ℝ E) (v : ι → a)
    (hv : LinearIndependent ℝ v) (Λ : StrongDual ℝ a)
    (hx : ∀ i, Λ (v i) ≠ 0) (hy : ∀ i, Λ (gramDual v i) ≠ 0) :
    (∑ J : Finset ι, (-1 : ℂ) ^ (Fintype.card ι - J.card) *
      (thetaOf a (fun i : J => v i) Λ)⁻¹ *
      (thetaOf a (fun i : {i // i ∉ J} => gramDual v i) Λ)⁻¹) = 0 := by
  let x (i : ι) := Complex.I * (Λ (v i) : ℂ)
  let y (i : ι) := Complex.I * (Λ (gramDual v i) : ℂ)
  let G := (Matrix.gram ℝ v).map Complex.ofRealHom
  have hx' (i : ι) : x i ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hx i))
  have hy' (i : ι) : y i ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hy i))
  have hxy : G *ᵥ y = x := by
    funext i
    have hi := congrArg Λ (eq_sum_smul_gramDual v hv i)
    simp only [map_sum, map_smul, smul_eq_mul] at hi
    rw [show x i = Complex.I * (Λ (v i) : ℂ) from rfl, hi, Complex.ofReal_sum, Finset.mul_sum]
    simp only [Matrix.mulVec_apply, dotProduct, G, Matrix.row_apply, Matrix.map_apply, Complex.ofRealHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      y, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  let A := diagonal (fun i => (x i)⁻¹) * G
  let B := diagonal (fun i => -(y i)⁻¹)
  have hkill : (A + B) *ᵥ y = 0 := by
    dsimp only [A, B]
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hxy]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.mulVec_diagonal,
      inv_mul_cancel₀ (hx' i), neg_mul, inv_mul_cancel₀ (hy' i), add_neg_cancel]
  have hzero : (A + B).det = 0 := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    hkill (mem_nonZeroDivisors_iff_ne_zero.mpr (hy' (Classical.choice ‹Nonempty ι›)))
  have hvol : (gramVolume v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (by rw [gramVolume_eq_sqrt]; exact (Real.sqrt_pos.mpr (det_gram_pos v hv)).ne')
  refine (mul_eq_zero.mp ?_).resolve_right hvol
  rw [Finset.sum_mul, ← hzero, det_add_eq_sum_rowPiecewise]
  apply Finset.sum_congr rfl
  intro J _
  have hg : (G.submatrix (Subtype.val : J → ι) Subtype.val).det =
      ((Matrix.gram ℝ (fun i : J => v i)).det : ℂ) := by
    exact (Complex.ofRealHom.map_det (Matrix.gram ℝ (fun i : J => v i))).symm
  have hcard : Fintype.card {i // i ∉ J} = Fintype.card ι - J.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (· ∈ J)
  have hm := congrArg Complex.ofReal (gramVolume_mul_mixed v hv J)
  simp only [Complex.ofReal_mul] at hm
  dsimp only [A, B]
  rw [det_rowPiecewise_diagonal, hg, Finset.prod_neg, Finset.card_univ, hcard,
    thetaOf_inv, thetaOf_inv, ← hm]
  change (-1 : ℂ) ^ (Fintype.card ι - J.card) *
      ((gramVolume (fun i : J => v i) : ℝ) * (∏ i : J, (x i)⁻¹)) *
      ((gramVolume (fun i : {i // i ∉ J} => gramDual v i) : ℝ) * (∏ i : {i // i ∉ J}, (y i)⁻¹)) *
      (gramVolume v : ℂ) = _
  ring

end Langlands.GMFamily
