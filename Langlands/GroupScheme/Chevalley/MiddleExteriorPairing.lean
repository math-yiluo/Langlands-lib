import Langlands.GroupScheme.Chevalley.MatrixExterior
import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # The matrix of the middle exterior pairing -/

noncomputable section

open Module Matrix
open scoped Classical

namespace Langlands.GroupScheme.Chevalley

variable (m : ℕ) (A : Type*) [CommRing A]

private abbrev CoordinateModule (N : ℕ) (R : Type*) := Fin N → R

private def volumeCoeff (N : ℕ) : ExteriorAlgebra A (CoordinateModule N A) →ₗ[A] A :=
  (Pi.basisFun A (Fin N)).ExteriorAlgebra.coord Finset.univ

/-- The pairing given by the volume coefficient of the product of two middle wedges. -/
def middleExteriorPairing : LinearMap.BilinForm A (⋀[A]^m (CoordinateModule (2 * m) A)) :=
  (exteriorPower.wedge A (CoordinateModule (2 * m) A) m m).compr₂
    ((volumeCoeff A (2 * m)).comp (Submodule.subtype _))

/-- The Gram matrix of `middleExteriorPairing` in the standard exterior basis. -/
def middleExteriorGram : Matrix (Set.powersetCard (Fin (2 * m)) m)
    (Set.powersetCard (Fin (2 * m)) m) A :=
  (middleExteriorPairing m A).toMatrix (matrixExteriorBasis (2 * m) m A)

private theorem topExteriorMap_eq (N : ℕ) (g : GL (Fin N) A) :
    exteriorPower.map N (Matrix.toLin' (g : Matrix (Fin N) (Fin N) A)) =
      (g : Matrix (Fin N) (Fin N) A).det • LinearMap.id := by
  let b := matrixExteriorBasis N N A
  let s : Set.powersetCard (Fin N) N := ⟨Finset.univ, by simp⟩
  have htop (t : Set.powersetCard (Fin N) N) : t = s :=
    Subtype.ext (Finset.eq_univ_of_card _ (by simp))
  have horder : Set.powersetCard.ofFinEmbEquiv.symm s = RelEmbedding.refl _ := by
    exact (Finset.orderEmbOfFin_unique' s.prop (fun _ => Finset.mem_univ _)).symm
  apply (LinearMap.toMatrix b b).injective
  rw [← exteriorGL_val, map_smul, LinearMap.toMatrix_id]
  ext i j
  rw [htop i, htop j, exteriorGL_apply, horder]
  simp [s]
  exact Matrix.det_transpose (g : Matrix (Fin N) (Fin N) A)

/-- The middle exterior action multiplies the wedge pairing by the determinant. -/
theorem middleExteriorGram_similitude (g : GL (Fin (2 * m)) A) :
    let X : Matrix (Set.powersetCard (Fin (2 * m)) m) _ A := exteriorGL (2 * m) m A g
    Xᵀ * middleExteriorGram m A * X =
      (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A).det • middleExteriorGram m A := by
  dsimp only
  let f := Matrix.toLin' (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A)
  let P := middleExteriorPairing m A
  let b := matrixExteriorBasis (2 * m) m A
  let Λ := exteriorPower.map m f
  change (LinearMap.toMatrix b b Λ)ᵀ * P.toMatrix b * LinearMap.toMatrix b b Λ =
    (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A).det • P.toMatrix b
  rw [← LinearMap.BilinForm.toMatrix_comp, ← map_smul]
  apply congrArg (LinearMap.BilinForm.toMatrix b)
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change P (Λ x) (Λ y) = (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A).det • P x y
  have htop (d : ℕ) (hd : d = 2 * m) (z : ⋀[A]^d (CoordinateModule (2 * m) A)) :
      (exteriorPower.map d f z : ExteriorAlgebra A (CoordinateModule (2 * m) A)) =
        (g : Matrix (Fin (2 * m)) (Fin (2 * m)) A).det •
          (z : ExteriorAlgebra A (CoordinateModule (2 * m) A)) := by
    subst d
    rw [show f = _ from rfl, topExteriorMap_eq A (2 * m) g]
    rfl
  have hw := htop (m + m) (two_mul m).symm
    (exteriorPower.wedge A (CoordinateModule (2 * m) A) m m x y)
  simp only [exteriorPower.coe_map, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, map_mul] at hw
  change volumeCoeff A (2 * m)
      ((Λ x : ExteriorAlgebra A (CoordinateModule (2 * m) A)) *
        (Λ y : ExteriorAlgebra A (CoordinateModule (2 * m) A))) = _
  simp only [Λ, exteriorPower.coe_map, ← map_mul]
  rw [← map_mul] at hw
  rw [hw, map_smul]
  rfl

private def middleComplement :
    Set.powersetCard (Fin (2 * m)) m ≃ Set.powersetCard (Fin (2 * m)) m :=
  Set.powersetCard.compl (by rw [Fintype.card_fin, two_mul])

private theorem middleExteriorGram_apply (s t : Set.powersetCard (Fin (2 * m)) m) :
    middleExteriorGram m A s t =
      if t = middleComplement m s then Set.powersetCard.sign s • (1 : A) else 0 := by
  let b := Pi.basisFun A (Fin (2 * m))
  have hcard : m + m = Fintype.card (Fin (2 * m)) := by rw [Fintype.card_fin, two_mul]
  have hcompl : Disjoint s.val t.val ↔ t = middleComplement m s :=
    disjoint_comm.trans (Set.powersetCard.disjoint_iff_eq_compl hcard)
  rw [middleExteriorGram, LinearMap.BilinForm.toMatrix_apply]
  change volumeCoeff A (2 * m)
      (exteriorPower.wedge A (CoordinateModule (2 * m) A) m m
        (b.exteriorPower m s) (b.exteriorPower m t)) = _
  by_cases h : Disjoint s.val t.val
  · have hunion : s.val ∪ t.val = Finset.univ :=
      Finset.eq_univ_of_card _ (by simp [Finset.card_union_of_disjoint h, ← two_mul])
    rw [ite_eq_left (hcompl.mp h), exteriorPower.wedge_apply_of_disjoint b hcard h, hunion]
    simp [volumeCoeff, b, map_zsmul_unit]
  · rw [ite_eq_right (mt hcompl.mpr h), exteriorPower.wedge_apply_of_not_disjoint b h]
    simp

/-- The Gram matrix of the middle wedge pairing is orthogonal. -/
theorem middleExteriorGram_transpose_mul :
    (middleExteriorGram m A)ᵀ * middleExteriorGram m A = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single ((middleComplement m).symm i)]
  · simp only [Matrix.transpose_apply, middleExteriorGram_apply, Equiv.apply_symm_apply, ite_true]
    by_cases h : j = i
    · subst j
      rw [ite_eq_left rfl, Matrix.one_apply_eq]
      rcases Int.units_eq_one_or (Set.powersetCard.sign ((middleComplement m).symm i)) with hs | hs
      · simp [hs]
      · simp [hs, Units.neg_smul]
    · simp [h, Ne.symm h]
  · intro k _ hk
    have h : i ≠ middleComplement m k := fun h' => hk
      ((Equiv.eq_symm_apply _).mpr h'.symm)
    simp [Matrix.transpose_apply, middleExteriorGram_apply, h]
  · simp

/-- The wedge Gram matrix as an element of the general linear group. -/
def middleExteriorGramUnit : GL (Set.powersetCard (Fin (2 * m)) m) A where
  val := middleExteriorGram m A
  inv := (middleExteriorGram m A)ᵀ
  val_inv := mul_eq_one_comm.mp (middleExteriorGram_transpose_mul m A)
  inv_val := middleExteriorGram_transpose_mul m A

private theorem volumeCoeff_anticomm
    (x y : Fin m → CoordinateModule (2 * m) A) :
    volumeCoeff A (2 * m) (ExteriorAlgebra.ιMulti A m x * ExteriorAlgebra.ιMulti A m y) =
      (-1 : A) ^ m •
        volumeCoeff A (2 * m) (ExteriorAlgebra.ιMulti A m y * ExteriorAlgebra.ιMulti A m x) := by
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm A x y, map_zsmul_unit]
  have hs : (-1 : A) ^ (m * m) = (-1) ^ m := by
    rw [pow_mul]
    rcases neg_one_pow_eq_or A m with h | h
    · calc
        ((-1 : A) ^ m) ^ m = 1 ^ m := congrArg (· ^ m) h
        _ = 1 := one_pow m
        _ = (-1) ^ m := h.symm
    · exact congrArg (· ^ m) h
  change ((↑((-1 : ℤˣ) ^ (m * m)) : ℤ) •
      volumeCoeff A (2 * m) (ExteriorAlgebra.ιMulti A m y * ExteriorAlgebra.ιMulti A m x)) = _
  rw [← Int.cast_smul_eq_zsmul A]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow,
    Int.cast_neg, Int.cast_one, hs]

private theorem middleExteriorGram_apply_ιMulti
    (s t : Set.powersetCard (Fin (2 * m)) m) :
    middleExteriorGram m A s t =
      volumeCoeff A (2 * m)
        (ExteriorAlgebra.ιMulti A m (Pi.basisFun A _ ∘ Set.powersetCard.ofFinEmbEquiv.symm s) *
          ExteriorAlgebra.ιMulti A m (Pi.basisFun A _ ∘ Set.powersetCard.ofFinEmbEquiv.symm t)) := by
  rw [middleExteriorGram, LinearMap.BilinForm.toMatrix_apply]
  let b := Pi.basisFun A (Fin (2 * m))
  change volumeCoeff A (2 * m)
      ((b.exteriorPower m s : ExteriorAlgebra A (CoordinateModule (2 * m) A)) *
        (b.exteriorPower m t : ExteriorAlgebra A (CoordinateModule (2 * m) A))) = _
  simp only [← ExteriorAlgebra.basis_eq_coe_basis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family]
  rfl

/-- Swapping the two middle wedges multiplies the Gram matrix by `(-1)^m`. -/
theorem middleExteriorGram_transpose :
    (middleExteriorGram m A)ᵀ = (-1 : A) ^ m • middleExteriorGram m A := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, middleExteriorGram_apply_ιMulti]
  exact volumeCoeff_anticomm m A _ _

/-- Squaring the wedge Gram matrix gives `(-1)^m` times the identity. -/
theorem middleExteriorGram_mul_self :
    middleExteriorGram m A * middleExteriorGram m A = (-1 : A) ^ m • 1 := by
  rw [← middleExteriorGram_transpose_mul m A, middleExteriorGram_transpose, Matrix.smul_mul,
    smul_smul, ← mul_pow]
  simp

/-- The standard wedge Gram matrix is preserved by change of coefficients. -/
theorem middleExteriorGram_map {A' : Type*} [CommRing A'] (f : A →+* A') :
    (middleExteriorGram m A).map f = middleExteriorGram m A' := by
  ext i j
  simp only [Matrix.map_apply, middleExteriorGram_apply]
  split
  · rw [map_zsmul_unit, map_one]
  · rw [map_zero]

end Langlands.GroupScheme.Chevalley
