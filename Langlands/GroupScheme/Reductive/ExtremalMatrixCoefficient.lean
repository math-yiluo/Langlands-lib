import Langlands.GroupScheme.MatrixRepresentation.DynamicExtremalLines
import Langlands.GroupScheme.Reductive.EigenMatrixCoefficient
import Langlands.GroupScheme.Dynamic.OppositeCellEmbedding

/-! # Normalized matrix coefficients from a unique smallest weight -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G H Q : GroupScheme (Spec (CommRingCat.of k))}

namespace MatrixRepresentation

variable (ρ : MatrixRepresentation G n)
  (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)

include hν in
/-- Inverting the cocharacter negates the diagonal weights of a representation. -/
theorem oppositeCocharacter_comp :
    Dynamic.oppositeCocharacter ν ≫ ρ =
      GeneralLinear.diagonalCocharacter n (CommRingCat.of k) (-e) := by
  rw [Dynamic.oppositeCocharacter, Category.assoc, hν,
    GeneralLinear.inv_comp_diagonalCocharacter]

/-- The maximum-weight character for the opposite parabolic at a unique
smallest-weight coordinate of the original cocharacter. -/
def oppositeMaximumWeightCharacter (iQ : Q ⟶ G)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ)
    (j : n) (hj : ∀ a, a ≠ j → e j < e a) : rationalCharacters Q :=
  maximumWeightCharacter ρ (Dynamic.oppositeCocharacter ν) (-e)
    (oppositeCocharacter_comp ρ ν e hν) iQ hQ j
    (fun a ha => neg_lt_neg (hj a ha))

theorem oppositeMaximumWeightCharacter_action (iQ : Q ⟶ G)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ)
    (j : n) (hj : ∀ a, a ≠ j → e j < e a)
    (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ Q.X) :
    (ρ.pointMatrix T (q ≫ iQ.hom.hom) : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
      (characterEval (oppositeMaximumWeightCharacter ρ ν e hν iQ hQ j hj) T q :
        Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)) :=
  maximumWeightCharacter_action ρ (Dynamic.oppositeCocharacter ν) (-e)
    (oppositeCocharacter_comp ρ ν e hν) iQ hQ j
    (fun a ha => neg_lt_neg (hj a ha)) T q

theorem oppositeMaximumWeightCharacter_eval (iQ : Q ⟶ G)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ)
    (j : n) (hj : ∀ a, a ≠ j → e j < e a)
    (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ Q.X) :
    (characterEval (oppositeMaximumWeightCharacter ρ ν e hν iQ hQ j hj) T q :
      Γ(T.left, ⊤)) =
        (ρ.pointMatrix T (q ≫ iQ.hom.hom) : Matrix n n Γ(T.left, ⊤)) j j :=
  maximumWeightCharacter_eval ρ (Dynamic.oppositeCocharacter ν) (-e)
    (oppositeCocharacter_comp ρ ν e hν) iQ hQ j
    (fun a ha => neg_lt_neg (hj a ha)) T q

end MatrixRepresentation

namespace AffineCoordinates

open MatrixRepresentation

omit [Fintype n] in
theorem scalarMap_single_one (T : Over (Spec (CommRingCat.of k))) (j : n) :
    (fun a => scalarMap T ((Pi.single j 1 : n → k) a)) =
      (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
  ext a
  by_cases ha : a = j <;> simp [ha]

variable [IsAffineHom G.X.hom]

local instance extremalMatrixCoefficientIsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The coordinate whose value is the diagonal matrix entry at `j`. -/
def diagonalMatrixCoefficient (ρ : MatrixRepresentation G n) (j : n) : algebra G :=
  matrixCoefficient G ρ (Pi.single j 1) (Pi.single j 1)

/-- The value on every relative test scheme is the original diagonal matrix entry. -/
theorem pointAlgebraHom_diagonalMatrixCoefficient (ρ : MatrixRepresentation G n) (j : n)
    (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) :
    pointAlgebraHom G T g (diagonalMatrixCoefficient ρ j) =
      (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) j j := by
  rw [diagonalMatrixCoefficient, pointAlgebraHom_matrixCoefficient, coefficientValue,
    scalarMap_single_one, Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply]

/-- The diagonal matrix coefficient is normalized on every test scheme. -/
theorem pointAlgebraHom_one_diagonalMatrixCoefficient (ρ : MatrixRepresentation G n) (j : n)
    (T : Over (Spec (CommRingCat.of k))) :
    pointAlgebraHom G T 1 (diagonalMatrixCoefficient ρ j) = 1 := by
  rw [pointAlgebraHom_diagonalMatrixCoefficient, map_one, Units.val_one,
    Matrix.one_apply_eq]
  rfl

variable (ρ : MatrixRepresentation G n)
  (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
  (i : H ⟶ G) (hH : (Dynamic.parabolic ν).IsRepresentedBy i)
  (j : n) (hj : ∀ a, a ≠ j → e j < e a)

variable [IsAffineHom H.X.hom]

local instance extremalMatrixCoefficientIsAffine2 : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

/-- A unique smallest coordinate gives a normalized left-covariant coordinate
for its constructed rational character. -/
theorem diagonalMatrixCoefficient_mem_leftCovariantSubspace :
    diagonalMatrixCoefficient ρ j ∈ leftCovariantSubspace i
      (characterCoordinate H (minimumWeightCharacter ρ ν e hν i hH j hj)) := by
  apply matrixCoefficient_mem_leftCovariantSubspace
  intro T h
  rw [scalarMap_single_one, pointValue, pointAlgebraHom_characterCoordinate]
  exact minimumWeightCharacter_action ρ ν e hν i hH j hj T h

variable [IsAffineHom Q.X.hom]

local instance extremalMatrixCoefficientIsAffine3 : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom

/-- The same coefficient satisfies inverse-right covariance on the opposite
parabolic, with the negative of its constructed maximum-weight character. -/
theorem pointAlgebraHom_mul_inv_diagonalMatrixCoefficient (iQ : Q ⟶ G)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ)
    (T : Over (Spec (CommRingCat.of k))) (q : T ⟶ Q.X) (g : T ⟶ G.X) :
    pointAlgebraHom G T (g * (q ≫ iQ.hom.hom)⁻¹) (diagonalMatrixCoefficient ρ j) =
      pointAlgebraHom Q T q
        (characterCoordinate Q (-oppositeMaximumWeightCharacter ρ ν e hν iQ hQ j hj)) *
          pointAlgebraHom G T g (diagonalMatrixCoefficient ρ j) := by
  apply pointAlgebraHom_mul_inv_matrixCoefficient
  intro T q
  rw [scalarMap_single_one, pointValue, pointAlgebraHom_characterCoordinate, characterEval_neg]
  simpa only [GrpObj.inv_comp, map_inv] using
    oppositeMaximumWeightCharacter_action ρ ν e hν iQ hQ j hj T q⁻¹

end AffineCoordinates

end Langlands.GroupScheme
