import Langlands.Global.ArchimedeanCartanFilteredCovariants

/-! # Strict filtered comparison for the actual Cartan tensor action -/

noncomputable section
universe u w
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An actual whole symmetric coefficient of degree zero is a scalar. -/
theorem exists_lieSymmetric_eq_algebraMap_of_mem_degree_zero
    {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n 0) :
    ∃ z : ℂ, algebraMap ℂ (LieSymmetricAlgebra K n) z = P := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have hl0 : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst l
    exact ⟨1, by simp⟩
  | zero => exact ⟨0, map_zero _⟩
  | add P Q hP hQ ihP ihQ =>
    obtain ⟨z, rfl⟩ := ihP
    obtain ⟨t, rfl⟩ := ihQ
    exact ⟨z + t, map_add _ _ _⟩
  | smul z P hP ih =>
    obtain ⟨t, rfl⟩ := ih
    exact ⟨z * t, by simp only [map_mul, Algebra.smul_def]⟩

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- Difference between acting by a whole symmetrization and multiplying by the
actual Cartan restriction before the tensor action. -/
def cartanTensorActionRestrictionError (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (P : LieSymmetricAlgebra K n) :
    CartanSymmetricCovariantModule K n τ →ₗ[ℂ] V :=
  (Algebra.lsmul ℂ ℂ V (lieSymmetricAlgebraSymmetrize K n P)).comp
      (cartanTensorAction K n τ j) -
    (cartanTensorAction K n τ j).comp
      (Algebra.lsmul ℂ ℂ (CartanSymmetricCovariantModule K n τ)
        (cartanSymmetricProjection K n P))

@[simp]
theorem cartanTensorActionRestrictionError_apply (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V) (P : LieSymmetricAlgebra K n)
    (x : CartanSymmetricCovariantModule K n τ) :
    cartanTensorActionRestrictionError K n τ j P x =
      lieSymmetricAlgebraSymmetrize K n P • cartanTensorAction K n τ j x -
        cartanTensorAction K n τ j (cartanSymmetricProjection K n P • x) := rfl

/-- The tensor action comparison has the same one-lower-degree bound as the
actual scalar comparison, after absorbing compact generators into the source. -/
theorem cartanTensorActionRestrictionError_mem (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (hj : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • v ∈ LinearMap.range j)
    {p q : ℕ} {P : LieSymmetricAlgebra K n}
    (hP : P ∈ lieSymmetricDegreeFiltration K n p)
    {x : CartanSymmetricCovariantModule K n τ}
    (hx : x ∈ cartanSymmetricTensorDegreeFiltration K n τ q) :
    cartanTensorActionRestrictionError K n τ j P x ∈
      envelopingDegreeFiltration K n (p + q - 1) • LinearMap.range j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q, hQ, v, rfl⟩ := hx
    simpa only [cartanTensorActionRestrictionError_apply, TensorProduct.smul_tmul',
      smul_eq_mul, cartanTensorAction_tmul] using
      lieSymmetrize_mul_cartan_action_sub_mem K n (LinearMap.range j) hj hP hQ
        (LinearMap.mem_range_self j v)
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using
      (envelopingDegreeFiltration K n (p + q - 1) • LinearMap.range j).add_mem ihx ihy
  | smul z x hx ih =>
    simpa only [map_smul] using
      (envelopingDegreeFiltration K n (p + q - 1) • LinearMap.range j).smul_mem z ih

/-- A scalar coefficient gives exact comparison, including the total degree-zero case. -/
theorem cartanTensorActionRestrictionError_eq_zero_of_degree_zero
    (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n 0) :
    cartanTensorActionRestrictionError K n τ j P = 0 := by
  obtain ⟨z, rfl⟩ := exists_lieSymmetric_eq_algebraMap_of_mem_degree_zero K n hP
  apply LinearMap.ext
  intro x
  simp only [cartanTensorActionRestrictionError_apply, lieSymmetricAlgebraSymmetrize_algebraMap,
    AlgHom.commutes, IsScalarTower.algebraMap_smul, map_smul, sub_self, LinearMap.zero_apply]

variable [NumberField K]

local instance (τ : ContinuousCompactRep K n) :
    SMul (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariants_groupInvariantModule K n τ).toSMul

/-- Actual full-group invariant coefficients act by actual central elements up to
the strict lower filtered piece on actual covariants. -/
theorem centralSymmetrize_cartanCovariant_action_sub_mem
    (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (hj : ∀ X : CompactComplexLieAlgebra K n, ∀ v ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • v ∈ LinearMap.range j)
    {p q : ℕ} (P : lieSymmetricGroupInvariants K n)
    (hP : P.val ∈ lieSymmetricDegreeFiltration K n p)
    {x : cartanSymmetricCovariants K n τ}
    (hx : x ∈ cartanSymmetricCovariantDegreeFiltration K n τ q) :
    (lieSymmetricGroupInvariantCentralSymmetrize K n P : EnvelopingAlgebra K n) •
        cartanTensorAction K n τ j x.val - cartanTensorAction K n τ j (P • x).val ∈
      envelopingDegreeFiltration K n (p + q - 1) • LinearMap.range j :=
  cartanTensorActionRestrictionError_mem K n τ j hj hP (x := x.val) hx

/-- At coefficient degree zero the actual central comparison is exact. -/
theorem centralSymmetrize_cartanCovariant_action_eq_of_degree_zero
    (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (P : lieSymmetricGroupInvariants K n)
    (hP : P.val ∈ lieSymmetricDegreeFiltration K n 0)
    (x : cartanSymmetricCovariants K n τ) :
    (lieSymmetricGroupInvariantCentralSymmetrize K n P : EnvelopingAlgebra K n) •
        cartanTensorAction K n τ j x.val = cartanTensorAction K n τ j (P • x).val := by
  apply sub_eq_zero.mp
  exact LinearMap.congr_fun
    (cartanTensorActionRestrictionError_eq_zero_of_degree_zero K n τ j hP) x.val

end Module

end Langlands.Global.ArchimedeanGL
