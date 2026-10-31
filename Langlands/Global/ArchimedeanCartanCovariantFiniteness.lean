import Langlands.Global.ArchimedeanCartanInvariantFiniteness
import Langlands.Global.ArchimedeanCartanCovariants

/-! # Actual Cartan covariants are finite over full-group invariants -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Full-group invariants act on compact invariants by the actual Cartan restriction. -/
instance cartanGroupInvariantCompactAlgebra :
    Algebra (lieSymmetricGroupInvariants K n) (cartanSymmetricCompactInvariants K n) :=
  (cartanGroupInvariantRestriction K n).toRingHom.toAlgebra

local instance (τ : ContinuousCompactRep K n) :
    SMul (cartanSymmetricCompactInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (Submodule.module (cartanSymmetricCovariants K n τ)).toSMul

/-- Full-group invariant coefficients act on the actual compact covariants by restriction. -/
instance cartanSymmetricCovariants_groupInvariantModule (τ : ContinuousCompactRep K n) :
    Module (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  Module.compHom _ (cartanGroupInvariantRestriction K n).toRingHom

local instance (τ : ContinuousCompactRep K n) :
    SMul (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariants_groupInvariantModule K n τ).toSMul

@[simp]
theorem cartanSymmetricCovariants_groupInvariant_smul
    (τ : ContinuousCompactRep K n) (P : lieSymmetricGroupInvariants K n)
    (x : cartanSymmetricCovariants K n τ) :
    P • x = cartanGroupInvariantRestriction K n P • x := rfl

@[simp]
theorem cartanSymmetricCovariants_groupInvariant_smul_coe
    (τ : ContinuousCompactRep K n) (P : lieSymmetricGroupInvariants K n)
    (x : cartanSymmetricCovariants K n τ) :
    (P • x).val = cartanSymmetricProjection K n P.val • x.val := rfl

/-- The compact and full-group coefficient actions on covariants form the actual scalar tower. -/
instance cartanSymmetricCovariants_groupInvariantTower (τ : ContinuousCompactRep K n) :
    IsScalarTower (lieSymmetricGroupInvariants K n) (cartanSymmetricCompactInvariants K n)
      (cartanSymmetricCovariants K n τ) :=
  IsScalarTower.of_compHom _ _ _

variable [NumberField K]

/-- Actual compact covariants are finite over the actual full-group invariant algebra. -/
theorem cartanSymmetricCovariants_groupInvariant_moduleFinite
    (τ : ContinuousCompactRep K n) :
    Module.Finite (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) := by
  let : Module.Finite (lieSymmetricGroupInvariants K n)
      (cartanSymmetricCompactInvariants K n) :=
    cartanGroupInvariantRestriction_finite K n
  let := cartanSymmetricCovariants_moduleFinite K n τ
  exact Module.Finite.trans (cartanSymmetricCompactInvariants K n)
    (cartanSymmetricCovariants K n τ)

end Langlands.Global.ArchimedeanGL
