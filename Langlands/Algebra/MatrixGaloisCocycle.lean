import Langlands.Algebra.MatrixAlgEquivInnerProof
import Langlands.Algebra.ScalarTwoCocycleLifts
import Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent
import Langlands.LinearAlgebra.SpecialLinearConjugationScalars
import Langlands.LinearAlgebra.GaloisVectorDescent

/-! # Actual scalar cocycles of semilinear matrix descent -/

noncomputable section
universe u v
open Matrix

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple.SemilinearGaloisAction

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {I : Type v} [Fintype I] [DecidableEq I]
  (ρ : SemilinearGaloisAction k L (Matrix I I L))

/-- Each element of a semilinear Galois ring action acts by an actual ring equivalence. -/
def actRingEquiv (σ : L ≃ₐ[k] L) : Matrix I I L ≃+* Matrix I I L :=
  { ρ.act σ with
    invFun := ρ.act σ⁻¹
    left_inv := fun X => by
      change ρ.act σ⁻¹ (ρ.act σ X) = X
      rw [← ρ.act_mul, inv_mul_cancel, ρ.act_one]
    right_inv := fun X => by
      change ρ.act σ (ρ.act σ⁻¹ X) = X
      rw [← ρ.act_mul, mul_inv_cancel, ρ.act_one] }

@[simp] theorem actRingEquiv_apply (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
    ρ.actRingEquiv σ X = ρ.act σ X := rfl

/-- Removing the coefficient automorphism leaves an actual linear matrix-algebra automorphism. -/
def linearPart (σ : L ≃ₐ[k] L) : Matrix I I L ≃ₐ[L] Matrix I I L where
  toRingEquiv := σ.symm.mapMatrix.toRingEquiv.trans (ρ.actRingEquiv σ)
  commutes' l := by
    change ρ.act σ (((algebraMap L (Matrix I I L) l) : Matrix I I L).map σ.symm) = _
    have hmap : ((algebraMap L (Matrix I I L) l) : Matrix I I L).map σ.symm =
        algebraMap L (Matrix I I L) (σ.symm l) := by
      ext i j
      by_cases h : i = j <;>
        simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, h]
    rw [hmap, ρ.act_algebraMap, σ.apply_symm_apply]

variable [Nonempty I]

/-- A chosen actual invertible matrix realizing the linear part of the action. -/
def innerMatrix (σ : L ≃ₐ[k] L) : GL I L :=
  (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv (ρ.linearPart σ)).choose

omit [Nonempty I] in
/-- The chosen inner matrix gives the complete semilinear action on every matrix. -/
theorem act_eq_innerMatrix (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
    ρ.act σ X = (ρ.innerMatrix σ : Matrix I I L) * X.map σ *
      (((ρ.innerMatrix σ)⁻¹ : GL I L) : Matrix I I L) := by
  have h := (Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv (ρ.linearPart σ)).choose_spec (X.map σ)
  change ρ.act σ ((X.map σ).map σ.symm) = _ at h
  have hid : (X.map σ).map σ.symm = X := by
    ext i j
    exact σ.symm_apply_apply (X i j)
  rw [hid] at h
  exact h

/-- Coefficient mapping gives the multiplicative action on actual invertible matrices. -/
@[instance_reducible]
def coefficientGLAction : MulDistribMulAction (L ≃ₐ[k] L) (GL I L) where
  smul σ X := GeneralLinearGroup.map σ.toRingHom X
  one_smul X := by ext i j; rfl
  mul_smul σ τ X := by ext i j; rfl
  smul_mul σ X Y := map_mul (GeneralLinearGroup.map σ.toRingHom) X Y
  smul_one σ := map_one (GeneralLinearGroup.map σ.toRingHom)

attribute [local instance] coefficientGLAction

omit [Nonempty I] in
@[simp] theorem coefficientGLAction_smul (σ : L ≃ₐ[k] L) (X : GL I L) :
    σ • X = GeneralLinearGroup.map σ.toRingHom X := rfl

omit [Nonempty I] in
@[simp] theorem coefficientGLAction_coe (σ : L ≃ₐ[k] L) (X : GL I L) :
    ((σ • X : GL I L) : Matrix I I L) = (X : Matrix I I L).map σ := rfl

/-- Unit scalars embed injectively into nonempty full general-linear groups. -/
theorem unit_scalar_injective : Function.Injective (GeneralLinearGroup.scalar I : Lˣ →* GL I L) := by
  intro a b h
  apply Units.ext
  let p : I := Classical.choice inferInstance
  have he := congrArg (fun X : GL I L => X p p) h
  simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using he

omit [Nonempty I] in
/-- Unit scalar matrices commute with every actual invertible matrix. -/
theorem unit_scalar_central (a : Lˣ) (X : GL I L) :
    Commute (GeneralLinearGroup.scalar I a) X := by
  apply Units.ext
  exact Matrix.scalar_comm _ (Commute.all _) _

omit [Nonempty I] in
/-- The scalar embedding intertwines coefficient automorphisms on both groups. -/
theorem coefficientGLAction_scalar (σ : L ≃ₐ[k] L) (a : Lˣ) :
    σ • GeneralLinearGroup.scalar I a = GeneralLinearGroup.scalar I (σ • a) := by
  exact GeneralLinearGroup.map_scalar σ.toRingHom a

omit [Nonempty I] in
/-- Products of inner matrices realize the product Galois action up to a unit scalar. -/
theorem exists_innerMatrix_mul_scalar (σ τ : L ≃ₐ[k] L) :
    ∃ a : Lˣ, ρ.innerMatrix σ * (σ • ρ.innerMatrix τ) =
      GeneralLinearGroup.scalar I a * ρ.innerMatrix (σ * τ) := by
  let Q := ρ.innerMatrix σ * (σ • ρ.innerMatrix τ)
  have hconj (X : Matrix I I L) :
      (Q : Matrix I I L) * X * ((Q⁻¹ : GL I L) : Matrix I I L) =
        (ρ.innerMatrix (σ * τ) : Matrix I I L) * X *
          (((ρ.innerMatrix (σ * τ))⁻¹ : GL I L) : Matrix I I L) := by
    obtain ⟨Y, rfl⟩ := (σ * τ).mapMatrix.surjective X
    have hY : (σ * τ).mapMatrix Y = Y.map (σ * τ) := rfl
    rw [hY]
    have he := (ρ.act_mul σ τ Y).symm
    rw [ρ.act_eq_innerMatrix σ, ρ.act_eq_innerMatrix τ, ρ.act_eq_innerMatrix (σ * τ)] at he
    simp only [Matrix.map_mul, Matrix.map_map] at he
    have hcomp : (σ : L → L) ∘ (τ : L → L) = (σ * τ : L ≃ₐ[k] L) := by
      funext a
      exact (AlgEquiv.mul_apply σ τ a).symm
    rw [hcomp] at he
    simpa only [Q, _root_.mul_inv_rev, Units.val_mul, ← smul_inv', coefficientGLAction_coe,
      Units.val_inv_eq_inv_val, Matrix.mul_assoc] using he
  obtain ⟨a, ha⟩ := Langlands.LinearAlgebra.SpecialLinearConjugation.exists_unit_scalar_of_conjugation_eq_conjugation
    Q (ρ.innerMatrix (σ * τ)) (fun g => by
      apply Units.ext
      exact hconj (g : Matrix I I L))
  exact ⟨a, ha.trans (unit_scalar_central a (ρ.innerMatrix (σ * τ))).symm.eq⟩

/-- The actual unit scalar defect of the chosen semilinear inner matrices. -/
def scalarDefect (σ τ : L ≃ₐ[k] L) : Lˣ :=
  (ρ.exists_innerMatrix_mul_scalar σ τ).choose

omit [Nonempty I] in
/-- The scalar defect records the actual multiplication of the chosen lifts. -/
theorem innerMatrix_mul (σ τ : L ≃ₐ[k] L) :
    ρ.innerMatrix σ * (σ • ρ.innerMatrix τ) =
      GeneralLinearGroup.scalar I (ρ.scalarDefect σ τ) * ρ.innerMatrix (σ * τ) :=
  (ρ.exists_innerMatrix_mul_scalar σ τ).choose_spec

/-- The actual scalar defect is a multiplicative scalar two-cocycle. -/
theorem scalarDefect_isTwoCocycle : Langlands.ScalarTwoCocycle.IsTwoCocycle ρ.scalarDefect :=
  Langlands.ScalarTwoCocycle.isTwoCocycle_of_lifts (GeneralLinearGroup.scalar I)
    unit_scalar_injective unit_scalar_central coefficientGLAction_scalar
    ρ.innerMatrix ρ.scalarDefect ρ.innerMatrix_mul

end Langlands.CentralSimple.SemilinearGaloisAction
