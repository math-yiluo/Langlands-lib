import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition

/-! # The complete family of coefficient projectors of a diagonalizable representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix Classical

namespace Langlands.GroupScheme.DiagonalizableProjectorWeights

open Diagonalizable.Averaging MatrixRepresentation.DiagonalizableCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (Diagonalizable.groupScheme R Λ).toGrp n)

/-- The matrix of coefficients of the character `m` in the universal representation. -/
def projector (m : Λ) : Matrix n n R := Matrix.of fun a b => coefficientColumn Λ ρ m b a

/-- A finite set containing every nonzero coefficient matrix. -/
def support : Finset Λ :=
  Finset.univ.biUnion fun ab : n × n => (universalMatrix Λ ρ ab.1 ab.2).coeff.support

/-- Every coefficient outside the finite support vanishes. -/
theorem projector_eq_zero {m : Λ} (hm : m ∉ support ρ) : projector ρ m = 0 := by
  ext a b
  by_contra h
  exact hm (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)

/-- The entries of the universal matrix decompose as the sums of the labelled monomials. -/
theorem universalMatrix_entry (a b : n) :
    universalMatrix Λ ρ a b = ∑ m ∈ support ρ, AddMonoidAlgebra.single m (projector ρ m a b) := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext m
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · change projector ρ m a b = 0
    rw [projector_eq_zero ρ hm]
    rfl

/-- All projectors of different weights are orthogonal and each is idempotent. -/
theorem projector_mul (m l : Λ) :
    projector ρ m * projector ρ l = if m = l then projector ρ m else 0 := by
  classical
  ext a b
  have h := congrArg (fun f : n → AddMonoidAlgebra R Λ => (f a).coeff m)
    (coefficientColumn_weight Λ ρ (universalPoint R Λ) l b)
  rw [pointsEquiv_universalPoint] at h
  change (∑ i, universalMatrix Λ ρ a i * AddMonoidAlgebra.single 0 (projector ρ l i b)).coeff m =
    (AddMonoidAlgebra.single l (1 : R) * AddMonoidAlgebra.single 0 (projector ρ l a b)).coeff m at h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.single_mul_single,
    add_zero, one_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] at h
  simp only [AddMonoidAlgebra.coeff_mul_single_zero] at h
  rw [Matrix.mul_apply]
  change ∑ i, (universalMatrix Λ ρ a i).coeff m * projector ρ l i b = _
  rw [h]
  by_cases he : m = l
  · subst l
    simp
  · simp [he, Ne.symm he]

/-- The projector family is complete, by evaluation at the trivial character. -/
theorem sum_projector : ∑ m ∈ support ρ, projector ρ m = 1 := by
  ext a b
  have h := congrArg (fun M : GL n R => M a b) (universalMatrix_evaluateOne Λ ρ)
  change (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom
      (universalMatrix Λ ρ a b) = (1 : Matrix n n R) a b at h
  rw [universalMatrix_entry, map_sum] at h
  rw [Matrix.sum_apply, ← h]
  refine Finset.sum_congr rfl fun m _ => ?_
  have he := Diagonalizable.lift_single R Λ (B := CommAlgCat.of R R)
    (1 : Multiplicative Λ →* Rˣ) m (projector ρ m a b)
  simpa only [MonoidHom.one_apply, Units.val_one, smul_eq_mul, mul_one] using he.symm

set_option maxHeartbeats 800000 in
/-- The entries of the representation on arbitrary tests are evaluated weight sums. -/
theorem pointMatrix_entry (T : Over (Spec R)) (x : T ⟶ (Diagonalizable.groupScheme R Λ).X)
    (a b : n) :
    ρ.pointMatrix T x a b = ∑ m ∈ support ρ, scalarMap T (projector ρ m a b) *
      (Diagonalizable.characterPointsEquiv R Λ T x (.ofAdd m) : Γ(T.left, ⊤)) := by
  have h := ρ.pointMatrix_naturality x (𝟙 (Diagonalizable.groupScheme R Λ).X)
  have hU : ρ.pointMatrix (Diagonalizable.groupScheme R Λ).X (𝟙 _) =
      Matrix.GeneralLinearGroup.map (DiagonalizableCharacter.sectionsIso R Λ).inv.hom.toRingHom
        (universalMatrix Λ ρ) :=
    ρ.pointMatrix_eq_affineMatrix (Diagonalizable.algebra R Λ) (𝟙 _)
  rw [Category.comp_id, hU] at h
  have he := congrArg (fun M : GL n Γ(T.left, ⊤) => M a b) h
  change ρ.pointMatrix T x a b =
    ((DiagonalizableCharacter.sectionsIso R Λ).inv ≫ ((algΓ R).map x).unop).hom
      (universalMatrix Λ ρ a b) at he
  rw [he, ← DiagonalizableCharacter.lift_characterPointsEquiv, universalMatrix_entry, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  let C := ((algΓ R).obj T).unop
  let χ : Multiplicative Λ →* Cˣ := Diagonalizable.characterPointsEquiv R Λ T x
  refine (Diagonalizable.lift_single R Λ (B := C) χ m (projector ρ m a b)).trans ?_
  exact Algebra.smul_def (projector ρ m a b) (χ (.ofAdd m) : C)

end Langlands.GroupScheme.DiagonalizableProjectorWeights
