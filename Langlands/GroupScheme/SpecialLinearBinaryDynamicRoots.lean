import Langlands.GroupScheme.SpecialLinearBinaryRootGroups
import Langlands.GroupScheme.SpecialLinearBinaryDiagonal
import Langlands.GroupScheme.Dynamic.Basic

/-! # Explicit contraction of the actual upper root of split SL₂ -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

section Matrices

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The actual determinant-one diagonal matrix contracting the upper root. -/
def contractingMatrix (t : Aˣ) : Matrix.SpecialLinearGroup (Fin 2) A :=
  BinaryUpper.diagonalMatrix t⁻¹

/-- The contracting diagonal matrices are multiplicative. -/
def contractingMatrixHom : Aˣ →* Matrix.SpecialLinearGroup (Fin 2) A :=
  BinaryUpper.diagonalMatrixHom.comp invMonoidHom

/-- The contracting diagonal matrix commutes with change of coefficient ring. -/
theorem map_contractingMatrix (f : A →+* B) (t : Aˣ) :
    Matrix.SpecialLinearGroup.map f (contractingMatrix t) =
      contractingMatrix (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  change (BinaryUpper.diagonalMatrix t⁻¹ : Matrix (Fin 2) (Fin 2) A).map f =
    (BinaryUpper.diagonalMatrix (Units.map f.toMonoidHom t)⁻¹ :
      Matrix (Fin 2) (Fin 2) B)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryUpper.diagonalMatrix]

/-- Diagonal conjugation multiplies the upper-root coordinate by the square of the unit. -/
theorem contractingMatrix_conjugate_upper (t : Aˣ) (x : A) :
    contractingMatrix t * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) x * (contractingMatrix t)⁻¹ =
        Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide)
          ((t : A) ^ 2 * x) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change !![(t : A), 0; 0, (↑t⁻¹ : A)] * Matrix.transvection (0 : Fin 2) 1 x =
    Matrix.transvection (0 : Fin 2) 1 ((t : A) ^ 2 * x) *
      !![(t : A), 0; 0, (↑t⁻¹ : A)]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, pow_two, mul_assoc, mul_comm]

end Matrices

section Schemes

variable (R : CommRingCat.{u})

/-- The contracting diagonal cocharacter on every actual relative test scheme. -/
def upperCocharacterPoints (T : Over (Spec R)) :
    (T ⟶ (Gm (Spec R)).X) →* (T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :=
  (SpecialLinear.pointsEquiv (Fin 2) R T).symm.toMonoidHom.comp
    (contractingMatrixHom.comp (Gm.pointsEquiv (Spec R) T).toMonoidHom)

theorem upperCocharacterPoints_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec R)).X) :
    upperCocharacterPoints R T' (a ≫ x) = a ≫ upperCocharacterPoints R T x := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R T').injective
  simp only [upperCocharacterPoints, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply,
    SpecialLinear.pointsEquiv_naturality, Gm.pointsEquiv_naturality]
  exact (map_contractingMatrix a.left.appTop.hom _).symm

/-- The actual ground-ring cocharacter `t ↦ diag(t,t⁻¹)` in split SL₂. -/
def upperCocharacter : (Gm (Spec R)).toGrp ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  homOfPoints (upperCocharacterPoints R) (upperCocharacterPoints_naturality R)

/-- The cocharacter has its prescribed diagonal matrix on every test scheme. -/
theorem pointsEquiv_upperCocharacter {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (x ≫ (upperCocharacter R).hom.hom) =
      contractingMatrix (Gm.pointsEquiv (Spec R) T x) := by
  rw [upperCocharacter, comp_homOfPoints]
  exact (SpecialLinear.pointsEquiv (Fin 2) R T).apply_symm_apply _

/-- The polynomial upper-root curve with coordinate `s² x` on `T × A¹`. -/
def upperContraction {T : Over (Spec R)} (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    T ⊗ AffineLine.scheme (Spec R) ⟶ (SpecialLinear.groupScheme (Fin 2) R).X :=
  (SpecialLinear.pointsEquiv (Fin 2) R _).symm
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide)
      (((snd T (AffineLine.scheme (Spec R))).left.appTop
          (AffineLine.coord (Spec R))) ^ 2 *
        (fst T (AffineLine.scheme (Spec R))).left.appTop
          ((VectorGroup.coordinates R 1 T x).toAdd 0)))

/-- Pulling back the contraction curve pulls back precisely its polynomial coefficient. -/
theorem pointsEquiv_comp_upperContraction {T T' : Over (Spec R)}
    (a : T' ⟶ T ⊗ AffineLine.scheme (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T' (a ≫ upperContraction R x) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide)
        (((a ≫ snd T (AffineLine.scheme (Spec R))).left.appTop
          (AffineLine.coord (Spec R))) ^ 2 *
          (a ≫ fst T (AffineLine.scheme (Spec R))).left.appTop
            ((VectorGroup.coordinates R 1 T x).toAdd 0)) := by
  rw [SpecialLinear.pointsEquiv_naturality]
  simp only [upperContraction, MulEquiv.apply_symm_apply, map_transvection,
    map_mul, map_pow, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The polynomial root curve extends the actual conjugation orbit on every test scheme. -/
theorem upperContraction_isOrbitExtension {T : Over (Spec R)}
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    Dynamic.IsOrbitExtension (upperCocharacter R)
      (x ≫ (upperMap R).hom.hom) (upperContraction R x) := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R _).injective
  rw [pointsEquiv_comp_upperContraction]
  simp only [Dynamic.orbit, map_mul, map_inv, pointsEquiv_upperCocharacter]
  rw [SpecialLinear.pointsEquiv_naturality, pointsEquiv_rootMap, map_transvection,
    contractingMatrix_conjugate_upper]
  congr 1
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]

/-- The same polynomial curve has the identity as its value at zero. -/
theorem upperContraction_evalZero {T : Over (Spec R)}
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    Dynamic.evalZero (upperContraction R x) = 1 := by
  apply (SpecialLinear.pointsEquiv (Fin 2) R _).injective
  rw [Dynamic.evalZero, pointsEquiv_comp_upperContraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- Every actual upper additive root point contracts to the identity under the
explicit diagonal cocharacter, over an arbitrary commutative base ring. -/
theorem upperRoot_range_le_dynamicUnipotent :
    SubgroupFunctor.range (upperMap R) ≤ Dynamic.unipotent (upperCocharacter R) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact ⟨upperContraction R x, upperContraction_isOrbitExtension R x,
    upperContraction_evalZero R x⟩

end Schemes

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
