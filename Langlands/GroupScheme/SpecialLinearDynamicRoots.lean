import Langlands.GroupScheme.SpecialLinearRootGroups
import Langlands.GroupScheme.Dynamic.Basic

/-! # Explicit contractions of actual coordinate-root maps in split SL_n -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.Root

variable {n : Type} [Fintype n] [DecidableEq n]

section Matrices

variable {A B : Type u} [CommRing A] [CommRing B] {i j : n}

/-- The determinant-one diagonal matrix with entries t, t⁻¹ at the two root positions. -/
def contractingMatrix (hij : i ≠ j) (t : Aˣ) : Matrix.SpecialLinearGroup n A :=
  ⟨Matrix.diagonal fun r => if r = i then (t : A) else if r = j then (↑t⁻¹ : A) else 1,
    by simp [Matrix.det_diagonal, Finset.prod_ite, Finset.filter_eq', hij.symm]⟩

/-- These actual determinant-one diagonal matrices are multiplicative in t. -/
def contractingMatrixHom (hij : i ≠ j) : Aˣ →* Matrix.SpecialLinearGroup n A where
  toFun := contractingMatrix hij
  map_one' := by
    apply Subtype.ext
    ext r s
    simp [contractingMatrix, Matrix.one_apply]
  map_mul' t v := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext r
    by_cases hri : r = i <;> by_cases hrj : r = j <;>
      simp [hri, hrj, hij.symm, mul_comm]

/-- The contracting diagonal matrix commutes with change of coefficient ring. -/
theorem map_contractingMatrix (f : A →+* B) (hij : i ≠ j) (t : Aˣ) :
    Matrix.SpecialLinearGroup.map f (contractingMatrix hij t) =
      contractingMatrix hij (Units.map f.toMonoidHom t) := by
  apply Subtype.ext
  change (Matrix.diagonal _).map f = Matrix.diagonal _
  ext r s
  by_cases hrs : r = s <;>
    simp [hrs, apply_ite f]

/-- Conjugation multiplies the chosen coordinate-root coefficient by the square of t. -/
theorem contractingMatrix_conjugate (hij : i ≠ j) (t : Aˣ) (x : A) :
    contractingMatrix hij t * Matrix.SpecialLinearGroup.transvection hij x *
        (contractingMatrix hij t)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij ((t : A) ^ 2 * x) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.transvection i j x =
    Matrix.transvection i j ((t : A) ^ 2 * x) * Matrix.diagonal _
  ext r s
  by_cases hrs : r = s <;> by_cases hri : r = i <;> by_cases hsj : s = j <;>
    simp_all [Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.transvection, Matrix.single_apply, Matrix.one_apply,
      pow_two, mul_assoc, mul_comm, eq_comm]

end Matrices

section Schemes

variable (R : CommRingCat.{u}) {i j : n} (hij : i ≠ j)

/-- The contracting diagonal cocharacter on every actual relative test scheme. -/
def cocharacterPoints (T : Over (Spec R)) :
    (T ⟶ (Gm (Spec R)).X) →* (T ⟶ (SpecialLinear.groupScheme n R).X) :=
  (SpecialLinear.pointsEquiv n R T).symm.toMonoidHom.comp
    ((contractingMatrixHom hij).comp (Gm.pointsEquiv (Spec R) T).toMonoidHom)

theorem cocharacterPoints_naturality {T T' : Over (Spec R)}
    (a : T' ⟶ T) (x : T ⟶ (Gm (Spec R)).X) :
    cocharacterPoints R hij T' (a ≫ x) = a ≫ cocharacterPoints R hij T x := by
  apply (SpecialLinear.pointsEquiv n R T').injective
  simp only [cocharacterPoints, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply,
    SpecialLinear.pointsEquiv_naturality, Gm.pointsEquiv_naturality]
  exact (map_contractingMatrix a.left.appTop.hom hij _).symm

/-- The actual ground-ring cocharacter with weights +1 and -1 at the root positions. -/
def cocharacter : (Gm (Spec R)).toGrp ⟶ SpecialLinear.groupScheme n R :=
  homOfPoints (cocharacterPoints R hij) (cocharacterPoints_naturality R hij)

/-- The cocharacter has its prescribed diagonal matrix on every test scheme. -/
theorem pointsEquiv_cocharacter {T : Over (Spec R)} (x : T ⟶ (Gm (Spec R)).X) :
    SpecialLinear.pointsEquiv n R T (x ≫ (cocharacter R hij).hom.hom) =
      contractingMatrix hij (Gm.pointsEquiv (Spec R) T x) := by
  rw [cocharacter, comp_homOfPoints]
  exact (SpecialLinear.pointsEquiv n R T).apply_symm_apply _

/-- The polynomial coordinate-root curve with coordinate `s² x` on `T × A¹`. -/
def contraction {T : Over (Spec R)} (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    T ⊗ AffineLine.scheme (Spec R) ⟶ (SpecialLinear.groupScheme n R).X :=
  (SpecialLinear.pointsEquiv n R _).symm
    (Matrix.SpecialLinearGroup.transvection hij
      (((snd T (AffineLine.scheme (Spec R))).left.appTop
          (AffineLine.coord (Spec R))) ^ 2 *
        (fst T (AffineLine.scheme (Spec R))).left.appTop
          ((VectorGroup.coordinates R 1 T x).toAdd 0)))

/-- Pulling back the contraction curve pulls back precisely its polynomial coefficient. -/
theorem pointsEquiv_comp_contraction {T T' : Over (Spec R)}
    (a : T' ⟶ T ⊗ AffineLine.scheme (Spec R))
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    SpecialLinear.pointsEquiv n R T' (a ≫ contraction R hij x) =
      Matrix.SpecialLinearGroup.transvection hij
        (((a ≫ snd T (AffineLine.scheme (Spec R))).left.appTop
          (AffineLine.coord (Spec R))) ^ 2 *
          (a ≫ fst T (AffineLine.scheme (Spec R))).left.appTop
            ((VectorGroup.coordinates R 1 T x).toAdd 0)) := by
  rw [SpecialLinear.pointsEquiv_naturality]
  simp only [contraction, MulEquiv.apply_symm_apply, map_transvection,
    map_mul, map_pow, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The polynomial root curve extends the actual conjugation orbit on every test scheme. -/
theorem contraction_isOrbitExtension {T : Over (Spec R)}
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    Dynamic.IsOrbitExtension (cocharacter R hij)
      (x ≫ (rootMap R hij).hom.hom) (contraction R hij x) := by
  apply (SpecialLinear.pointsEquiv n R _).injective
  rw [pointsEquiv_comp_contraction]
  simp only [Dynamic.orbit, map_mul, map_inv, pointsEquiv_cocharacter]
  rw [SpecialLinear.pointsEquiv_naturality, pointsEquiv_rootMap, map_transvection,
    contractingMatrix_conjugate]
  congr 1
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]

/-- The same polynomial curve has the identity as its value at zero. -/
theorem contraction_evalZero {T : Over (Spec R)}
    (x : T ⟶ (VectorGroup.groupScheme R 1).X) :
    Dynamic.evalZero (contraction R hij x) = 1 := by
  apply (SpecialLinear.pointsEquiv n R _).injective
  rw [Dynamic.evalZero, pointsEquiv_comp_contraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- Every actual coordinate-root point contracts to the identity under the
explicit diagonal cocharacter, over an arbitrary commutative base ring. -/
theorem root_range_le_dynamicUnipotent :
    SubgroupFunctor.range (rootMap R hij) ≤ Dynamic.unipotent (cocharacter R hij) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact ⟨contraction R hij x, contraction_isOrbitExtension R hij x,
    contraction_evalZero R hij x⟩

end Schemes

end Langlands.GroupScheme.SpecialLinear.Root
