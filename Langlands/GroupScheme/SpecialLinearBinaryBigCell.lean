import Langlands.GroupScheme.SpecialLinearBinaryUpper
import Langlands.GroupScheme.InnerAutomorphism

/-! # The explicit binary special-linear unit cell -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

section Matrices

variable {A : Type u} [CommRing A]

/-- The determinant-one Weyl matrix, over any commutative ring. -/
def weylMatrix : Matrix.SpecialLinearGroup (Fin 2) A :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- Conjugation by the Weyl matrix exchanges the two triangular subgroups. -/
theorem weylMatrix_conj (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    ((weylMatrix * g * weylMatrix⁻¹ : Matrix.SpecialLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) = !![g 1 1, -g 1 0; -g 0 1, g 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- The inverse conjugate has the complementary diagonal entries. -/
theorem weylMatrix_conj_inv (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    (((weylMatrix * g * weylMatrix⁻¹)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) A) :
      Matrix (Fin 2) (Fin 2) A) = !![g 0 0, g 1 0; g 0 1, g 1 1] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  change !![(↑(weylMatrix (A := A) * g * (weylMatrix (A := A))⁻¹) :
      Matrix (Fin 2) (Fin 2) A) 1 1,
    -(↑(weylMatrix (A := A) * g * (weylMatrix (A := A))⁻¹) :
      Matrix (Fin 2) (Fin 2) A) 0 1;
    -(↑(weylMatrix (A := A) * g * (weylMatrix (A := A))⁻¹) :
      Matrix (Fin 2) (Fin 2) A) 1 0,
    (↑(weylMatrix (A := A) * g * (weylMatrix (A := A))⁻¹) :
      Matrix (Fin 2) (Fin 2) A) 0 0] = _
  rw [weylMatrix_conj]
  simp

/-- Applying Weyl conjugation twice is the identity on matrices. -/
theorem weylMatrix_conj_conj (g : Matrix.SpecialLinearGroup (Fin 2) A) :
    weylMatrix * (weylMatrix * g * weylMatrix⁻¹) * weylMatrix⁻¹ = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (↑(weylMatrix (A := A) *
    (weylMatrix (A := A) * g * (weylMatrix (A := A))⁻¹) *
      (weylMatrix (A := A))⁻¹) :
    Matrix (Fin 2) (Fin 2) A) i j = g i j
  rw [weylMatrix_conj]
  have e := weylMatrix_conj g
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 1) e
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => -M 1 0) e
  · simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) A => -M 0 1) e
  · exact congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) e

/-- The upper unipotent with the given off-diagonal entry. -/
def upperUnipotent (t : A) : subgroup A :=
  ⟨⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩, by simp⟩

/-- Right multiplication by the inverse conjugate scales the last entry by the same
last-diagonal character as left multiplication by the original upper subgroup. -/
theorem mul_inv_conjugate_lastEntry (g : Matrix.SpecialLinearGroup (Fin 2) A)
    (h : subgroup A) :
    (g * (weylMatrix * h.val * weylMatrix⁻¹)⁻¹) 1 1 = h.val 1 1 * g 1 1 := by
  change ((g : Matrix (Fin 2) (Fin 2) A) *
    (↑((weylMatrix (A := A) * h.val * (weylMatrix (A := A))⁻¹)⁻¹) :
      Matrix (Fin 2) (Fin 2) A)) 1 1 = _
  rw [weylMatrix_conj_inv]
  have hh : h.val 1 0 = 0 := h.property
  simp [Matrix.mul_apply, Fin.sum_univ_two, hh, mul_comm]

/-- A unit bottom-right entry gives two global upper-subgroup factors. -/
theorem exists_upper_factors_of_isUnit (g : Matrix.SpecialLinearGroup (Fin 2) A)
    (hg : IsUnit (g 1 1)) :
    ∃ a b : subgroup A, g = a.val * (weylMatrix * b.val * weylMatrix⁻¹)⁻¹ := by
  obtain ⟨v, hv⟩ := hg
  let b := upperUnipotent ((↑v⁻¹ : A) * g 1 0)
  let c := weylMatrix * b.val * weylMatrix⁻¹
  have ha : (g * c) 1 0 = 0 := by
    change ((g : Matrix (Fin 2) (Fin 2) A) * (c : Matrix (Fin 2) (Fin 2) A)) 1 0 = 0
    dsimp only [c]
    rw [weylMatrix_conj]
    simp [Matrix.mul_apply, Fin.sum_univ_two, b, upperUnipotent, ← hv]
  exact ⟨⟨g * c, ha⟩, b, (mul_inv_cancel_right g c).symm⟩

/-- A common upper and conjugate-upper matrix has zero upper off-diagonal entry. -/
theorem upperEntry_eq_zero_of_eq_conjugate (a b : subgroup A)
    (h : a.val = weylMatrix * b.val * weylMatrix⁻¹) : a.val 0 1 = 0 := by
  have e := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) A => g 0 1) h
  have e' := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1)
    (weylMatrix_conj b.val)
  have hb : b.val 1 0 = 0 := b.property
  exact e.trans (e'.trans (by simp [hb]))

end Matrices

section SchemePoints

variable (R : CommRingCat.{u})

/-- The actual base-valued Weyl point. -/
def weylPoint : Over.mk (𝟙 (Spec R)) ⟶
    (SpecialLinear.groupScheme (Fin 2) R).X :=
  (SpecialLinear.pointsEquiv (Fin 2) R _).symm weylMatrix

/-- Pulling back the Weyl point gives the same matrix on every relative test scheme. -/
theorem pointsEquiv_constant_weylPoint (T : Over (Spec R)) :
    SpecialLinear.pointsEquiv (Fin 2) R T
      ((SpecialLinear.groupScheme (Fin 2) R).constantPoint (weylPoint R) T) =
      weylMatrix := by
  unfold GroupScheme.constantPoint
  rw [SpecialLinear.pointsEquiv_naturality]
  simp only [weylPoint, MulEquiv.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMatrix]

/-- The conjugate of the actual upper subgroup by the actual Weyl point. -/
def conjugateInclusion : groupScheme R ⟶ SpecialLinear.groupScheme (Fin 2) R :=
  inclusion R ≫ ((SpecialLinear.groupScheme (Fin 2) R).innerIso (weylPoint R)).hom

/-- The conjugate inclusion acts by the prescribed matrix conjugation on every test. -/
theorem pointsEquiv_conjugateInclusion (T : Over (Spec R))
    (h : T ⟶ (groupScheme R).X) :
    SpecialLinear.pointsEquiv (Fin 2) R T (h ≫ (conjugateInclusion R).hom.hom) =
      weylMatrix * (pointsEquiv R T h).val * weylMatrix⁻¹ := by
  change SpecialLinear.pointsEquiv (Fin 2) R T
    ((h ≫ (inclusion R).hom.hom) ≫
      ((SpecialLinear.groupScheme (Fin 2) R).innerIso (weylPoint R)).hom.hom.hom) = _
  rw [GroupScheme.comp_innerIso_hom, map_mul, map_mul, map_inv,
    pointsEquiv_constant_weylPoint, pointsEquiv_inclusion]

/-- The conjugate subgroup is exactly the lower-triangular subgroup on all tests. -/
theorem mem_range_conjugateInclusion {T : Over (Spec R)}
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :
    g ∈ (SubgroupFunctor.range (conjugateInclusion R)).carrier T ↔
      SpecialLinear.pointsEquiv (Fin 2) R T g 0 1 = 0 := by
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    rw [pointsEquiv_conjugateInclusion]
    rw [weylMatrix_conj]
    simpa using congrArg Neg.neg (pointsEquiv R T h).property
  · intro hg
    let a := SpecialLinear.pointsEquiv (Fin 2) R T g
    let b : subgroup Γ(T.left, ⊤) :=
      ⟨weylMatrix * a * weylMatrix⁻¹, by
        rw [mem_subgroup]
        rw [weylMatrix_conj]
        simpa [a] using congrArg Neg.neg hg⟩
    refine ⟨(pointsEquiv R T).symm b, ?_⟩
    apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
    rw [pointsEquiv_conjugateInclusion, MulEquiv.apply_symm_apply]
    exact weylMatrix_conj_conj a

/-- Every point in the unit locus admits global factors on its original test scheme. -/
theorem exists_factors_of_lastEntry_isUnit (T : Over (Spec R))
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X)
    (hg : IsUnit (SpecialLinear.pointsEquiv (Fin 2) R T g 1 1)) :
    ∃ a b : T ⟶ (groupScheme R).X,
      g = (a ≫ (inclusion R).hom.hom) *
        (b ≫ (conjugateInclusion R).hom.hom)⁻¹ := by
  obtain ⟨a, b, hab⟩ := exists_upper_factors_of_isUnit
    (SpecialLinear.pointsEquiv (Fin 2) R T g) hg
  refine ⟨(pointsEquiv R T).symm a, (pointsEquiv R T).symm b, ?_⟩
  apply (SpecialLinear.pointsEquiv (Fin 2) R T).injective
  rw [map_mul, map_inv, pointsEquiv_inclusion, pointsEquiv_conjugateInclusion,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact hab

end SchemePoints

section Coordinates

variable (k : Type u) [Field k]

local instance instIsAffineSpecialLinearLeft_specialLinearBinaryBigCell :
    IsAffine (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.left :=
  SpecialLinear.isAffine_groupScheme _ _

local instance instIsAffineBinaryUpperLeft_specialLinearBinaryBigCell :
    IsAffine (groupScheme (CommRingCat.of k)).X.left :=
  isAffine_groupScheme _

local instance instIsAffineHomBinaryUpper_specialLinearBinaryBigCell :
    IsAffineHom (groupScheme (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme _

local instance instIsAffineHomSpecialLinear_specialLinearBinaryBigCell :
    IsAffineHom (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X.hom :=
  SpecialLinear.isAffineHom_groupScheme _ _

/-- The bottom-right entry as an element of the actual affine coordinate algebra. -/
def lastEntryCoordinate :
    AffineCoordinates.algebra (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) :=
  (affineRowPolynomial (n := Fin 2) (k := k) 1) (X 1)

/-- Evaluation of this affine coordinate is the bottom-right matrix entry. -/
theorem pointAlgebraHom_lastEntryCoordinate (T : Over (Spec (CommRingCat.of k)))
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X) :
    AffineCoordinates.pointAlgebraHom _ T g (lastEntryCoordinate k) =
      SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of k) T g 1 1 := by
  rw [lastEntryCoordinate, pointAlgebraHom_affineRowPolynomial, aeval_X]

/-- The entry coordinate is left covariant for the actual last-diagonal character. -/
theorem lastEntryCoordinate_mem_leftCovariant :
    lastEntryCoordinate k ∈ AffineCoordinates.leftCovariantSubspace
      (inclusion (CommRingCat.of k)) (characterCoordinate k) := by
  apply AffineCoordinates.mem_leftCovariantSubspace_of_points
  intro T h g
  rw [pointAlgebraHom_lastEntryCoordinate, pointAlgebraHom_lastEntryCoordinate,
    pointAlgebraHom_characterCoordinate, map_mul]
  exact upper_mul_bottomRow _ _ (inclusion_lowerEntry _ T h) 1

/-- Right covariance uses the identical character and the actual conjugate subgroup. -/
theorem pointAlgebraHom_lastEntryCoordinate_mul_inv (T : Over (Spec (CommRingCat.of k)))
    (h : T ⟶ (groupScheme (CommRingCat.of k)).X)
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X) :
    AffineCoordinates.pointAlgebraHom _ T
      (g * (h ≫ (conjugateInclusion (CommRingCat.of k)).hom.hom)⁻¹)
      (lastEntryCoordinate k) =
    AffineCoordinates.pointAlgebraHom _ T h (characterCoordinate k) *
      AffineCoordinates.pointAlgebraHom _ T g (lastEntryCoordinate k) := by
  rw [pointAlgebraHom_lastEntryCoordinate, pointAlgebraHom_lastEntryCoordinate,
    pointAlgebraHom_characterCoordinate, pointsEquiv_inclusion,
    map_mul, map_inv, pointsEquiv_conjugateInclusion]
  exact mul_inv_conjugate_lastEntry _ _

/-- The chosen coordinate is normalized at the identity on every test scheme. -/
theorem pointAlgebraHom_lastEntryCoordinate_one (T : Over (Spec (CommRingCat.of k))) :
    AffineCoordinates.pointAlgebraHom _ T 1 (lastEntryCoordinate k) = 1 := by
  rw [pointAlgebraHom_lastEntryCoordinate, map_one]
  simp

/-- The coordinate unit condition gives the full inverse-factor decomposition. -/
theorem exists_factors_of_unit_lastEntryCoordinate (T : Over (Spec (CommRingCat.of k)))
    (g : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)).X)
    (hg : IsUnit (AffineCoordinates.pointAlgebraHom _ T g (lastEntryCoordinate k))) :
    ∃ a b : T ⟶ (groupScheme (CommRingCat.of k)).X,
      g = (a ≫ (inclusion (CommRingCat.of k)).hom.hom) *
        (b ≫ (conjugateInclusion (CommRingCat.of k)).hom.hom)⁻¹ := by
  rw [pointAlgebraHom_lastEntryCoordinate] at hg
  exact exists_factors_of_lastEntry_isUnit _ T g hg

end Coordinates

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
