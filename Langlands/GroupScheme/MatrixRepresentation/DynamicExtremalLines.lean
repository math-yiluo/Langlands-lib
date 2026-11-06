import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.MatrixRepresentation.CoordinateLineCharacter
import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.HomogeneousCharacterCoordinates

/-! # Extremal coordinate lines of dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Vanishing off a coordinate column on all tests implies preservation of
that coordinate line with a global unit scalar. -/
theorem preservesCoordinateLine_of_column_eq_zero (ρ : MatrixRepresentation H n) (j : n)
    (hz : ∀ (T : Over (Spec R)) (h : T ⟶ H.X) (a : n), a ≠ j →
      (ρ.pointMatrix T h : Matrix n n Γ(T.left, ⊤)) a j = 0) :
    ρ.PreservesCoordinateLine j := by
  intro T h
  let M := ρ.pointMatrix T h
  have hm : (M : Matrix n n Γ(T.left, ⊤)) j j *
      ((M⁻¹ : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) j j = 1 := by
    have hm := congrArg (fun U : GL n Γ(T.left, ⊤) =>
      (U : Matrix n n Γ(T.left, ⊤)) j j)
      (mul_inv_cancel M)
    rw [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single j] at hm
    · exact hm
    · intro a _ haj
      rw [show ((M⁻¹ : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) a j = 0 by
        simpa only [M, map_inv] using hz T h⁻¹ a haj, mul_zero]
    · simp
  refine ⟨⟨(M : Matrix n n Γ(T.left, ⊤)) j j, ((M⁻¹ : GL n Γ(T.left, ⊤)) : Matrix n n Γ(T.left, ⊤)) j j,
    hm, by rw [mul_comm]; exact hm⟩, ?_⟩
  ext a
  by_cases ha : a = j
  · subst a
    simp [M]
  · simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      Pi.single_eq_of_ne ha, smul_eq_mul, mul_zero]
    exact hz T h a ha

variable (ρ : MatrixRepresentation G n) (ν : (Gm (Spec R)).toGrp ⟶ G)
  (e : n → ℤ) (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n R e)

include hν in
/-- Every dynamic parabolic point acts by a block triangular matrix with
the prescribed cocharacter weights, on every scheme test. -/
theorem pointMatrix_entry_eq_zero_of_mem_parabolic
    {T : Over (Spec R)} {g : T ⟶ G.X}
    (hg : g ∈ (Dynamic.parabolic ν).carrier T) {a b : n} (hab : e a < e b) :
    (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) a b = 0 := by
  have h := Dynamic.parabolic_le_comap ν ρ T hg
  rw [SubgroupFunctor.mem_comap, hν, GeneralLinear.parabolic_diagonalCocharacter,
    GeneralLinear.mem_blockParabolic] at h
  exact h a b hab

variable (i : H ⟶ G) (hH : (Dynamic.parabolic ν).IsRepresentedBy i) (j : n)

include hν hH in
/-- A coordinate of strictly largest weight is a parabolic eigenline. -/
theorem preservesCoordinateLine_of_unique_maximum
    (hj : ∀ a, a ≠ j → e a < e j) :
    (ρ.restrict i).PreservesCoordinateLine j := by
  apply preservesCoordinateLine_of_column_eq_zero
  intro T h a ha
  rw [pointMatrix_restrict]
  exact pointMatrix_entry_eq_zero_of_mem_parabolic ρ ν e hν (hH.pointsEquiv T h).property
    (hj a ha)

include hν hH in
/-- A coordinate of strictly smallest weight is an eigenline in the dual
parabolic representation. -/
theorem dual_preservesCoordinateLine_of_unique_minimum
    (hj : ∀ a, a ≠ j → e j < e a) :
    (ρ.restrict i).dual.PreservesCoordinateLine j := by
  apply preservesCoordinateLine_of_column_eq_zero
  intro T h a ha
  rw [dual_pointMatrix, GeneralLinear.matrixContragredient_coe, Matrix.transpose_apply,
    ← map_inv, pointMatrix_restrict]
  exact pointMatrix_entry_eq_zero_of_mem_parabolic ρ ν e hν
    (hH.pointsEquiv T h⁻¹).property (hj a ha)

/-- The rational character on a unique largest-weight coordinate line. -/
def maximumWeightCharacter (hj : ∀ a, a ≠ j → e a < e j) : rationalCharacters H :=
  (ρ.restrict i).coordinateLineRationalCharacter j
    (preservesCoordinateLine_of_unique_maximum ρ ν e hν i hH j hj)

/-- The rational character of the coordinate covector of a unique smallest
weight, obtained by negating the dual-line character. -/
def minimumWeightCharacter (hj : ∀ a, a ≠ j → e j < e a) : rationalCharacters H :=
  -(ρ.restrict i).dual.coordinateLineRationalCharacter j
    (dual_preservesCoordinateLine_of_unique_minimum ρ ν e hν i hH j hj)

theorem maximumWeightCharacter_action (hj : ∀ a, a ≠ j → e a < e j)
    (T : Over (Spec R)) (h : T ⟶ H.X) :
    (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      (characterEval (maximumWeightCharacter ρ ν e hν i hH j hj) T h : Γ(T.left, ⊤)) •
        (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
  exact (ρ.restrict i).coordinateLineCharacter_action j
    (preservesCoordinateLine_of_unique_maximum ρ ν e hν i hH j hj) T h

theorem minimumWeightCharacter_action (hj : ∀ a, a ≠ j → e j < e a)
    (T : Over (Spec R)) (h : T ⟶ H.X) :
    (Pi.single j 1 : n → Γ(T.left, ⊤)) ᵥ*
        (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) =
      (characterEval (minimumWeightCharacter ρ ν e hν i hH j hj) T h : Γ(T.left, ⊤)) •
        (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
  have hact := (ρ.restrict i).dual.coordinateLineCharacter_action j
    (dual_preservesCoordinateLine_of_unique_minimum ρ ν e hν i hH j hj) T h⁻¹
  rw [dual_pointMatrix, map_inv, GeneralLinear.matrixContragredient_coe, inv_inv,
    pointMatrix_restrict] at hact
  simpa only [minimumWeightCharacter, characterEval_neg, map_inv,
    Matrix.mulVec_single_one, Matrix.single_one_vecMul, Matrix.row, Matrix.col,
    Matrix.transpose_transpose, Matrix.transpose_apply, mul_one, one_mul] using hact

theorem maximumWeightCharacter_eval (hj : ∀ a, a ≠ j → e a < e j)
    (T : Over (Spec R)) (h : T ⟶ H.X) :
    (characterEval (maximumWeightCharacter ρ ν e hν i hH j hj) T h : Γ(T.left, ⊤)) =
      (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) j j := by
  have hact := congrFun (maximumWeightCharacter_action ρ ν e hν i hH j hj T h) j
  simpa using hact.symm

theorem minimumWeightCharacter_eval (hj : ∀ a, a ≠ j → e j < e a)
    (T : Over (Spec R)) (h : T ⟶ H.X) :
    (characterEval (minimumWeightCharacter ρ ν e hν i hH j hj) T h : Γ(T.left, ⊤)) =
      (ρ.pointMatrix T (h ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) j j := by
  have hact := congrFun (minimumWeightCharacter_action ρ ν e hν i hH j hj T h) j
  simpa using hact.symm

end Langlands.GroupScheme.MatrixRepresentation
