import Langlands.Representation.AffineGeneric.Genericity

/-!
# The product of the cyclic coordinates is a determinant

For `ϖ : Fˣ`, define `D(g) = ∏ᵢ aᵢ(g - 1)` using the cyclic coordinates. If `ϖ` is a
uniformizer and `Y` lies in the radical `𝔓` of the standard Iwahori order, then
`∏ᵢ aᵢ(Y) = res((-1)^m ϖ⁻¹ det Y)`. Consequently, for a uniformizer `ϖ`,
`D(x⁻¹ g x) = D(g)` whenever both `g` and `x⁻¹ g x` lie in `I⁺`.

The proof permutes the rows of `Y` cyclically and divides the row coming from the last row of
`Y` by `ϖ`. The resulting matrix `A` lies in the Iwahori order `𝔄`, its diagonal entries have
residues `aᵢ(Y)`, and the determinant of an element of `𝔄` reduces to the product of the
residues of its diagonal entries.
-/

noncomputable section

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear

universe u

variable {F : Type u} [Field F] [ValuativeRel F] {m : ℕ}

/-! ### Determinants on the Iwahori order -/

/-- The residue of the determinant of an element of the Iwahori order is the product of the
residues of its diagonal entries. -/
theorem IsIwahoriOrder.resOf_det {A : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hA : IsIwahoriOrder A) : resOf A.det = ∏ i, resOf (A i i) := by
  let A' : Matrix (Fin (m + 1)) (Fin (m + 1)) (integers F) := fun i j =>
    ⟨A i j, (Valuation.mem_integer_iff _ _).mpr (hA i j).1⟩
  have hA' : (integers F).subtype.mapMatrix A' = A := by
    ext i j
    rfl
  have hres : ∀ i j, IsLocalRing.residue (integers F) (A' i j) = resOf (A i j) :=
    fun i j => (resOf_coe (A' i j)).symm
  have hdet : A.det = ((A'.det : integers F) : F) := by
    rw [← hA']
    exact (RingHom.map_det (integers F).subtype A').symm
  rw [hdet, resOf_coe, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_isUpperTriangular]
  · simp only [Matrix.map_apply, hres]
  · intro i j hij
    simp only [Matrix.map_apply, hres]
    exact resOf_of_lt_one ((hA i j).2 hij)

/-! ### The determinant identity -/

omit [ValuativeRel F] in
theorem prod_weight (ϖ : Fˣ) : ∏ i, weight ϖ (i : Fin (m + 1)) = (ϖ : F)⁻¹ := by
  rw [Fin.prod_univ_castSucc]
  have h : ∀ i : Fin m, weight ϖ i.castSucc = 1 := fun i => by
    unfold weight
    simp [(Fin.castSucc_lt_last i).ne]
  simp only [h, Finset.prod_const_one, one_mul]
  unfold weight
  simp

theorem finRotate_symm_zero : (finRotate (m + 1)).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq, finRotate_last]

variable {ϖ : Fˣ} (hϖ : GeneralLinear.Iwasawa.IsUniformizingElement (valuation F) ϖ)
include hϖ

/-- For a uniformizer `ϖ`, cyclically permuting the rows of `Y ∈ 𝔓` and dividing the row
that came from the last row by `ϖ` gives a matrix in the Iwahori order. -/
theorem isIwahoriOrder_rotate {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F}
    (hY : IsIwahoriRadical Y) :
    IsIwahoriOrder (Matrix.of fun i j =>
      weight ϖ ((finRotate (m + 1)).symm i) * Y ((finRotate (m + 1)).symm i) j) := by
  intro i j
  simp only [Matrix.of_apply]
  by_cases hi : i = 0
  · subst hi
    rw [finRotate_symm_zero]
    unfold weight
    simp only [↓reduceIte]
    exact ⟨val_inv_mul_le_one hϖ ((hY _ _).2 (Fin.le_last _)),
      fun h => absurd h (Fin.not_lt_zero j)⟩
  · have hne : (finRotate (m + 1)).symm i ≠ Fin.last m := fun h => hi (by
      rw [← (finRotate (m + 1)).apply_symm_apply i, h, finRotate_last])
    have hval : (i : ℕ) = ((finRotate (m + 1)).symm i : ℕ) + 1 := by
      rw [← finRotate_val_of_ne_last hne, Equiv.apply_symm_apply]
    unfold weight
    simp only [hne, ↓reduceIte, one_mul]
    refine ⟨(hY _ _).1, fun hji => (hY _ _).2 ?_⟩
    rw [Fin.le_def]
    rw [Fin.lt_def] at hji
    omega

/-- **Determinant identity.** For a uniformizer `ϖ` and `Y ∈ 𝔓`,
`∏ᵢ aᵢ(Y) = res((-1)^m ϖ⁻¹ det Y)`. -/
theorem prod_coord {Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F} (hY : IsIwahoriRadical Y) :
    ∏ i, coord ϖ Y i = resOf ((-1) ^ m * ((ϖ : F)⁻¹ * Y.det)) := by
  set ρ := finRotate (m + 1)
  let A : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    Matrix.of fun i j => weight ϖ (ρ.symm i) * Y (ρ.symm i) j
  have hA : IsIwahoriOrder A := isIwahoriOrder_rotate hϖ hY
  have hdiag : ∀ i, resOf (A i i) = coord ϖ Y (ρ.symm i) := by
    intro i
    simp only [A, Matrix.of_apply, coord]
    rw [Equiv.apply_symm_apply]
  have hdetA : A.det = (-1) ^ m * ((ϖ : F)⁻¹ * Y.det) := by
    have hA_eq : A = Matrix.of fun i j => weight ϖ (ρ.symm i) * (Y.submatrix ρ.symm id) i j := rfl
    rw [hA_eq, Matrix.det_mul_column, Matrix.det_permute,
      Equiv.prod_comp ρ.symm (fun i => weight ϖ i), prod_weight, Equiv.Perm.sign_symm,
      sign_finRotate]
    simp only [add_tsub_cancel_right, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    ring
  rw [← Equiv.prod_comp ρ.symm (coord ϖ Y)]
  simp_rw [← hdiag]
  rw [← hA.resOf_det, hdetA]

omit hϖ

/-! ### The invariant `D` on `I⁺` -/

variable (ϖ)

/-- The product `D(g) = ∏ᵢ aᵢ(g - 1)` of the cyclic coordinates of `g`. -/
def coordProd (g : GeneralLinear (m + 1) F) : Residue F :=
  ∏ i, groupCoord ϖ g i

variable {ϖ}

omit [ValuativeRel F] in
theorem det_conj_sub_one (x g : GeneralLinear (m + 1) F) :
    (((x⁻¹ * g * x : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1).det =
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1).det := by
  have he : ((x⁻¹ * g * x : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1 =
      ((x⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1) * (x : Matrix _ _ F) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, coe_inv_mul_coe]
    simp only [Matrix.GeneralLinearGroup.coe_mul]
  rw [he, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) (Matrix.det _), mul_assoc,
    ← Matrix.det_mul, coe_inv_mul_coe, Matrix.det_one, mul_one]

include hϖ

theorem coordProd_eq {g : GeneralLinear (m + 1) F} (hg : g ∈ iwahoriRadical m) :
    coordProd ϖ g =
      resOf ((-1) ^ m * ((ϖ : F)⁻¹ * ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) - 1).det)) :=
  prod_coord hϖ hg.1

/-- For a uniformizer `ϖ`, `D` takes equal values on conjugate elements of `I⁺`. -/
theorem coordProd_conj {x g : GeneralLinear (m + 1) F} (hg : g ∈ iwahoriRadical m)
    (hxg : x⁻¹ * g * x ∈ iwahoriRadical m) :
    coordProd ϖ (x⁻¹ * g * x) = coordProd ϖ g := by
  rw [coordProd_eq hϖ hg, coordProd_eq hϖ hxg, det_conj_sub_one]

end Langlands.AffineGeneric
