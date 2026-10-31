import Langlands.Algebra.SymmetricTensorHomogeneous
import Langlands.Global.ArchimedeanCartanCovariantFiniteness

/-! # Actual homogeneous invariant coefficients and compact covariants -/

noncomputable section
universe u
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Global.ArchimedeanGL

open Langlands.Algebra.SymmetricGrading

variable (K : Type u) [Field K] (n : ℕ)

/-- Canonical homogeneous projection on the actual whole symmetric algebra. -/
abbrev lieSymmetricComponent (d : ℕ) :
    LieSymmetricAlgebra K n →ₗ[ℂ] LieSymmetricAlgebra K n :=
  component ℂ (ComplexLieAlgebra K n) d

/-- Canonical homogeneous projection on the actual Cartan symmetric algebra. -/
abbrev cartanSymmetricComponent (d : ℕ) :
    CartanSymmetricAlgebra K n →ₗ[ℂ] CartanSymmetricAlgebra K n :=
  component ℂ (ComplexCartanComplement K n) d

theorem lieSymmetricComponent_inclusion (d : ℕ) (P : CartanSymmetricAlgebra K n) :
    lieSymmetricComponent K n d (cartanSymmetricInclusion K n P) =
      cartanSymmetricInclusion K n (cartanSymmetricComponent K n d P) :=
  component_lift ℂ (ComplexCartanComplement K n) (cartanComplexInclusion K n) d P

theorem cartanSymmetricComponent_projection (d : ℕ) (P : LieSymmetricAlgebra K n) :
    cartanSymmetricComponent K n d (cartanSymmetricProjection K n P) =
      cartanSymmetricProjection K n (lieSymmetricComponent K n d P) :=
  component_lift ℂ (ComplexLieAlgebra K n) (cartanComplexProjection K n) d P

theorem lieSymmetricComponent_conjugation (d : ℕ) (g : InfiniteAdelicGL K n)
    (P : LieSymmetricAlgebra K n) :
    lieSymmetricComponent K n d (lieSymmetricConjugation K n g P) =
      lieSymmetricConjugation K n g (lieSymmetricComponent K n d P) :=
  component_lift ℂ (ComplexLieAlgebra K n)
    (complexLieConjugation K n g).toLinearMap d P

theorem cartanSymmetricComponent_conjugation (d : ℕ) (k : standardInfiniteCompact K n)
    (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricComponent K n d (cartanSymmetricConjugation K n k P) =
      cartanSymmetricConjugation K n k (cartanSymmetricComponent K n d P) :=
  component_lift ℂ (ComplexCartanComplement K n)
    (cartanComplexConjugation K n k).toLinearMap d P

/-- Homogeneous projection restricted to actual full-group invariant coefficients. -/
def lieSymmetricGroupInvariantComponent (d : ℕ) :
    lieSymmetricGroupInvariants K n →ₗ[ℂ] lieSymmetricGroupInvariants K n :=
  ((lieSymmetricComponent K n d).comp
    (lieSymmetricGroupInvariants K n).val.toLinearMap).codRestrict
      (lieSymmetricGroupInvariants K n).toSubmodule (by
        intro P g
        change lieSymmetricConjugation K n g (lieSymmetricComponent K n d P.val) =
          lieSymmetricComponent K n d P.val
        rw [← lieSymmetricComponent_conjugation, P.property g])

@[simp]
theorem lieSymmetricGroupInvariantComponent_coe (d : ℕ)
    (P : lieSymmetricGroupInvariants K n) :
    (lieSymmetricGroupInvariantComponent K n d P).val =
      lieSymmetricComponent K n d P.val := rfl

/-- Homogeneous projection restricted to actual complementary compact invariants. -/
def cartanSymmetricCompactInvariantComponent (d : ℕ) :
    cartanSymmetricCompactInvariants K n →ₗ[ℂ] cartanSymmetricCompactInvariants K n :=
  ((cartanSymmetricComponent K n d).comp
    (cartanSymmetricCompactInvariants K n).val.toLinearMap).codRestrict
      (cartanSymmetricCompactInvariants K n).toSubmodule (by
        intro P k
        change cartanSymmetricConjugation K n k (cartanSymmetricComponent K n d P.val) =
          cartanSymmetricComponent K n d P.val
        rw [← cartanSymmetricComponent_conjugation, P.property k])

@[simp]
theorem cartanSymmetricCompactInvariantComponent_coe (d : ℕ)
    (P : cartanSymmetricCompactInvariants K n) :
    (cartanSymmetricCompactInvariantComponent K n d P).val =
      cartanSymmetricComponent K n d P.val := rfl

theorem cartanGroupInvariantRestriction_component (d : ℕ)
    (P : lieSymmetricGroupInvariants K n) :
    cartanSymmetricCompactInvariantComponent K n d (cartanGroupInvariantRestriction K n P) =
      cartanGroupInvariantRestriction K n (lieSymmetricGroupInvariantComponent K n d P) := by
  apply Subtype.ext
  exact cartanSymmetricComponent_projection K n d P.val

theorem lieSymmetricGroupInvariantComponent_homogeneous (d : ℕ)
    (P : lieSymmetricGroupInvariants K n) :
    lieSymmetricComponent K n d (lieSymmetricGroupInvariantComponent K n d P).val =
      (lieSymmetricGroupInvariantComponent K n d P).val := by
  simp only [lieSymmetricGroupInvariantComponent_coe, lieSymmetricComponent,
    component_component, ↓reduceIte]

/-- Canonical homogeneous projection on the actual complementary tensor module. -/
abbrev cartanSymmetricTensorComponent (τ : ContinuousCompactRep K n) (d : ℕ) :
    CartanSymmetricCovariantModule K n τ →ₗ[ℂ] CartanSymmetricCovariantModule K n τ :=
  tensorComponent ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) d

theorem cartanSymmetricTensorComponent_conjugation (τ : ContinuousCompactRep K n)
    (d : ℕ) (k : standardInfiniteCompact K n) (x : CartanSymmetricCovariantModule K n τ) :
    cartanSymmetricTensorComponent K n τ d
        (cartanSymmetricCovariantRepresentation K n τ k x) =
      cartanSymmetricCovariantRepresentation K n τ k
        (cartanSymmetricTensorComponent K n τ d x) :=
  tensorComponent_natural ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ)
    (cartanComplexConjugation K n k).toLinearMap (τ.toRepresentation k) d x

/-- Degree projection on the actual full compact covariants; it is complex linear. -/
def cartanSymmetricCovariantComponent (τ : ContinuousCompactRep K n) (d : ℕ) :
    cartanSymmetricCovariants K n τ →ₗ[ℂ] cartanSymmetricCovariants K n τ :=
  ((cartanSymmetricTensorComponent K n τ d).comp
    ((cartanSymmetricCovariants K n τ).restrictScalars ℂ).subtype).codRestrict
      ((cartanSymmetricCovariants K n τ).restrictScalars ℂ) (by
        intro x k
        change cartanSymmetricCovariantRepresentation K n τ k
            (cartanSymmetricTensorComponent K n τ d x.val) =
          cartanSymmetricTensorComponent K n τ d x.val
        rw [← cartanSymmetricTensorComponent_conjugation, x.property k])

@[simp]
theorem cartanSymmetricCovariantComponent_coe (τ : ContinuousCompactRep K n)
    (d : ℕ) (x : cartanSymmetricCovariants K n τ) :
    (cartanSymmetricCovariantComponent K n τ d x).val =
      cartanSymmetricTensorComponent K n τ d x.val := rfl

/-- Homogeneity is defined by the actual canonical tensor projection. -/
def IsHomogeneousCartanCovariant (τ : ContinuousCompactRep K n) (d : ℕ)
    (x : cartanSymmetricCovariants K n τ) : Prop :=
  IsHomogeneousTensor ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) d x.val

theorem cartanSymmetricCovariantComponent_homogeneous (τ : ContinuousCompactRep K n)
    (d : ℕ) (x : cartanSymmetricCovariants K n τ) :
    IsHomogeneousCartanCovariant K n τ d (cartanSymmetricCovariantComponent K n τ d x) :=
  tensorComponent_isHomogeneous ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) d x.val

theorem cartanSymmetricCovariantComponent_component (τ : ContinuousCompactRep K n)
    (d e : ℕ) (x : cartanSymmetricCovariants K n τ) :
    cartanSymmetricCovariantComponent K n τ d (cartanSymmetricCovariantComponent K n τ e x) =
      if e = d then cartanSymmetricCovariantComponent K n τ e x else 0 := by
  apply Subtype.ext
  simpa only [cartanSymmetricCovariantComponent_coe, Submodule.coe_zero, apply_ite] using
    tensorComponent_component ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) d e x.val

/-- Every actual compact covariant has a finite canonical homogeneous decomposition. -/
theorem exists_cartanSymmetricCovariantComponent_bound (τ : ContinuousCompactRep K n)
    (x : cartanSymmetricCovariants K n τ) :
    ∃ D : ℕ, (∀ d, D < d → cartanSymmetricCovariantComponent K n τ d x = 0) ∧
      ∑ d ∈ Finset.range (D + 1), cartanSymmetricCovariantComponent K n τ d x = x := by
  obtain ⟨D, hz, hs⟩ :=
    exists_tensorComponent_bound ℂ (ComplexCartanComplement K n) (Fin τ.dim → ℂ) x.val
  refine ⟨D, fun d hd => Subtype.ext (hz d hd), ?_⟩
  apply Subtype.ext
  simpa only [Submodule.coe_sum, cartanSymmetricCovariantComponent_coe] using hs

local instance (τ : ContinuousCompactRep K n) :
    SMul (lieSymmetricGroupInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariants_groupInvariantModule K n τ).toSMul

theorem cartanSymmetricCovariantComponent_smul_of_homogeneous
    (τ : ContinuousCompactRep K n) (d : ℕ) (P : lieSymmetricGroupInvariants K n)
    {e : ℕ} {x : cartanSymmetricCovariants K n τ}
    (hx : IsHomogeneousCartanCovariant K n τ e x) :
    cartanSymmetricCovariantComponent K n τ d (P • x) =
      if e ≤ d then lieSymmetricGroupInvariantComponent K n (d - e) P • x else 0 := by
  apply Subtype.ext
  simp only [cartanSymmetricCovariantComponent_coe, apply_ite, Submodule.coe_zero,
    cartanSymmetricCovariants_groupInvariant_smul_coe, lieSymmetricGroupInvariantComponent_coe]
  rw [tensorComponent_smul_of_isHomogeneous ℂ (ComplexCartanComplement K n)
    (Fin τ.dim → ℂ) d _ hx, cartanSymmetricComponent_projection]
  split_ifs <;> rfl

end Langlands.Global.ArchimedeanGL
