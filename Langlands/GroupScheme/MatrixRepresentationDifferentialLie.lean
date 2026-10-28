import Langlands.GroupScheme.MatrixRepresentationDifferentialConjugation
import Mathlib.Algebra.Lie.Matrix

/-! # Lie differentials of actual algebraic matrix representations -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.GeneralLinear.DualNumber

variable {n : Type v} {S : Type u} [CommRing S]

/-- Epsilon matrices preserve subtraction. -/
theorem epsilonMatrix_sub (X Y : Matrix n n S) :
    epsilonMatrix (X - Y) = epsilonMatrix X - epsilonMatrix Y := by
  apply Matrix.ext
  intro i j
  simp only [epsilonMatrix_apply, Matrix.sub_apply, TrivSqZeroExt.inr_sub]

/-- An epsilon matrix is the scalar epsilon times its constant lift. -/
theorem epsilonMatrix_eq_smul (X : Matrix n n S) :
    epsilonMatrix X =
      (DualNumber.eps : DualNumber S) • X.map (TrivSqZeroExt.inlHom S S) := by
  apply Matrix.ext
  intro i j
  simp only [epsilonMatrix_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, DualNumber.eps, TrivSqZeroExt.inlHom_apply,
    TrivSqZeroExt.inr_mul_inl, op_smul_eq_mul, one_mul]

variable [Fintype n] [DecidableEq n]

/-- First-order conjugation of a constant matrix is its commutator correction. -/
theorem matrixUnit_conjugate_constant (X Y : Matrix n n S) :
    (matrixUnit X : Matrix n n (DualNumber S)) *
        Y.map (TrivSqZeroExt.inlHom S S) *
        (((matrixUnit X)⁻¹ : GL n (DualNumber S)) : Matrix n n (DualNumber S)) =
      Y.map (TrivSqZeroExt.inlHom S S) + epsilonMatrix (X * Y - Y * X) := by
  rw [matrixUnit_val, matrixUnit_inv_val, add_mul, one_mul,
    epsilonMatrix_mul_constantMatrix, mul_sub, mul_one, add_mul,
    constantMatrix_mul_epsilonMatrix, epsilonMatrix_mul, add_zero, epsilonMatrix_sub]
  abel

end Langlands.GroupScheme.GeneralLinear.DualNumber

namespace Langlands.GroupScheme.MatrixRepresentation

open GeneralLinear GeneralLinear.DualNumber

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : CommRingCat.{u}}
variable {n m k : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- Naturality and linearity determine the differential on epsilon matrices. -/
theorem differential_epsilonMatrix (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.differential (DualNumber S) (epsilonMatrix X) =
      epsilonMatrix (ρ.differential S X) := by
  rw [epsilonMatrix_eq_smul, map_smul]
  have hc := ρ.differential_naturality (TrivSqZeroExt.inlAlgHom R S S) X
  change ρ.differential (DualNumber S) (X.map (TrivSqZeroExt.inlHom S S)) =
    (ρ.differential S X).map (TrivSqZeroExt.inlHom S S) at hc
  rw [hc, ← epsilonMatrix_eq_smul]

/-- The actual algebraic dual-number differential preserves matrix commutators. -/
theorem differential_commutator (ρ : MatrixRepresentation (groupScheme n R) m)
    (X Y : Matrix n n S) :
    ρ.differential S (X * Y - Y * X) =
      ρ.differential S X * ρ.differential S Y -
        ρ.differential S Y * ρ.differential S X := by
  have hc := ρ.differential_naturality (TrivSqZeroExt.inlAlgHom R S S) Y
  change ρ.differential (DualNumber S) (Y.map (TrivSqZeroExt.inlHom S S)) =
    (ρ.differential S Y).map (TrivSqZeroExt.inlHom S S) at hc
  have h := differential_conjugate (S := DualNumber S) ρ (matrixUnit X)
    (Y.map (TrivSqZeroExt.inlHom S S))
  rw [matrixUnit_conjugate_constant, map_add, differential_epsilonMatrix, hc,
    matrixPointsHom_matrixUnit, matrixUnit_conjugate_constant] at h
  have he := add_left_cancel h
  apply Matrix.ext
  intro i j
  exact congrArg TrivSqZeroExt.snd (congrArg (fun A => A i j) he)

/-- The existing constructed differential also preserves the standard Lie bracket. -/
theorem differential_lie (ρ : MatrixRepresentation (groupScheme n R) m)
    (X Y : Matrix n n S) :
    ρ.differential S ⁅X, Y⁆ = ⁅ρ.differential S X, ρ.differential S Y⁆ :=
  ρ.differential_commutator X Y

/-- Bundle the same differential as a Lie algebra homomorphism. -/
def differentialLieHom (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] : Matrix n n S →ₗ⁅S⁆ Matrix m m S :=
  { ρ.differential S with map_lie' := fun {X Y} => ρ.differential_lie X Y }

@[simp]
theorem differentialLieHom_toLinearMap
    (ρ : MatrixRepresentation (groupScheme n R) m) :
    (ρ.differentialLieHom S).toLinearMap = ρ.differential S := rfl

@[simp]
theorem differentialLieHom_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) :
    ρ.differentialLieHom S X = ρ.differential S X := rfl

/-- The constructed differential acts on the coordinate module as a genuine Lie action. -/
def differentialLieAction (ρ : MatrixRepresentation (groupScheme n R) m) (S : Type u)
    [CommRing S] [Algebra R S] :
    Matrix n n S →ₗ⁅S⁆ Module.End S (m → S) :=
  (lieEquivMatrix' (R := S) (n := m)).symm.toLieHom.comp (ρ.differentialLieHom S)

@[simp]
theorem differentialLieAction_toLinearMap
    (ρ : MatrixRepresentation (groupScheme n R) m) :
    (ρ.differentialLieAction S).toLinearMap = ρ.differentialAction S := rfl

@[simp]
theorem differentialLieAction_apply (ρ : MatrixRepresentation (groupScheme n R) m)
    (X : Matrix n n S) (v : m → S) :
    ρ.differentialLieAction S X v = ρ.differential S X *ᵥ v := rfl

/-- The Lie chain rule retains the actual point-map chain rule. -/
theorem differentialLieHom_comp (ρ : MatrixRepresentation (groupScheme n R) m)
    (σ : MatrixRepresentation (groupScheme m R) k) :
    differentialLieHom (ρ ≫ σ) S =
      (σ.differentialLieHom S).comp (ρ.differentialLieHom S) := by
  ext X i j
  exact congrArg (fun A : Matrix k k S => A i j) (differential_comp ρ σ X)

end Langlands.GroupScheme.MatrixRepresentation
