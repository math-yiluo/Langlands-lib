import Langlands.Representation.Jacquet.Localization
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar extension of character-one Jacquet quotients -/

noncomputable section

open scoped TensorProduct

namespace Langlands.Jacquet.Localization

universe uR uB uG uV

variable {R : Type uR} [CommRing R]
  {B : Type uB} [CommRing B] [Algebra R B]
  {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

local instance scalarTensorAddCommGroup : AddCommGroup (B ⊗[R] V) :=
  TensorProduct.addCommGroup

variable (ρ : Representation R G V) (τ : Representation B G (B ⊗[R] V))
  (U : Subgroup G)
  (hτ : ∀ (u : U) (b : B) (v : V), τ u (b ⊗ₜ[R] v) = b ⊗ₜ[R] ρ u v)

/-- The scalar-extended quotient map kills exactly the required radical relations. -/
def scalarExtensionToTensor :
    Coinvariants τ U 1 →ₗ[B] B ⊗[R] Coinvariants ρ U 1 :=
  lift τ U 1 ((mk ρ U 1).baseChange B) (by
    intro u t
    induction t using TensorProduct.inductionOn with
    | tmul b v =>
      simp only [hτ, LinearMap.baseChange_tmul, mk_apply_subgroup,
        MonoidHom.one_apply, Units.val_one, one_smul]
    | add t s ht hs => simpa only [map_add, smul_add] using congrArg₂ (· + ·) ht hs)

@[simp]
theorem scalarExtensionToTensor_mk_tmul (b : B) (v : V) :
    scalarExtensionToTensor ρ τ U hτ (mk τ U 1 (b ⊗ₜ[R] v)) =
      b ⊗ₜ[R] mk ρ U 1 v := rfl

/-- The original carrier maps to the scalar-extended quotient through the unit tensor. -/
def scalarExtensionUnit :
    Coinvariants ρ U 1 →ₗ[R] Coinvariants τ U 1 :=
  lift ρ U 1
    ((mk τ U 1).restrictScalars R ∘ₗ TensorProduct.mk R B V 1) (by
      intro u v
      change mk τ U 1 (1 ⊗ₜ[R] ρ u v) = (1 : R) • mk τ U 1 (1 ⊗ₜ[R] v)
      rw [← hτ u 1 v, mk_apply_subgroup]
      simp)

@[simp]
theorem scalarExtensionUnit_mk (v : V) :
    scalarExtensionUnit ρ τ U hτ (mk ρ U 1 v) =
      mk τ U 1 (1 ⊗ₜ[R] v) := rfl

/-- Extend the unit-tensor quotient map by the native coefficient scalars. -/
def tensorToScalarExtension :
    B ⊗[R] Coinvariants ρ U 1 →ₗ[B] Coinvariants τ U 1 :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : B →ₗ[B] B).smulRight (scalarExtensionUnit ρ τ U hτ))

@[simp]
theorem tensorToScalarExtension_tmul_mk (b : B) (v : V) :
    tensorToScalarExtension ρ τ U hτ (b ⊗ₜ[R] mk ρ U 1 v) =
      mk τ U 1 (b ⊗ₜ[R] v) := by
  change b • mk τ U 1 (1 ⊗ₜ[R] v) = _
  rw [← map_smul]
  simp [TensorProduct.smul_tmul']

/-- Character-one coinvariants commute with scalar extension when the subgroup
action on tensors is the scalar extension of the original action. No flatness,
smoothness, finite-dimensionality or Noetherian hypothesis is needed. -/
def scalarExtensionEquiv :
    Coinvariants τ U 1 ≃ₗ[B] B ⊗[R] Coinvariants ρ U 1 :=
  LinearEquiv.ofLinearMap
    (scalarExtensionToTensor ρ τ U hτ)
    (tensorToScalarExtension ρ τ U hτ)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b q
      obtain ⟨v, rfl⟩ := mk_surjective ρ U 1 q
      change scalarExtensionToTensor ρ τ U hτ
        (tensorToScalarExtension ρ τ U hτ (b ⊗ₜ[R] mk ρ U 1 v)) =
          b ⊗ₜ[R] mk ρ U 1 v
      rw [tensorToScalarExtension_tmul_mk, scalarExtensionToTensor_mk_tmul])
    (by
      apply hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro b v
      change tensorToScalarExtension ρ τ U hτ
        (scalarExtensionToTensor ρ τ U hτ (mk τ U 1 (b ⊗ₜ[R] v))) =
          mk τ U 1 (b ⊗ₜ[R] v)
      rw [scalarExtensionToTensor_mk_tmul, tensorToScalarExtension_tmul_mk])

@[simp]
theorem scalarExtensionEquiv_mk_tmul (b : B) (v : V) :
    scalarExtensionEquiv ρ τ U hτ (mk τ U 1 (b ⊗ₜ[R] v)) =
      b ⊗ₜ[R] mk ρ U 1 v := rfl

@[simp]
theorem scalarExtensionEquiv_symm_tmul_mk (b : B) (v : V) :
    (scalarExtensionEquiv ρ τ U hτ).symm (b ⊗ₜ[R] mk ρ U 1 v) =
      mk τ U 1 (b ⊗ₜ[R] v) :=
  tensorToScalarExtension_tmul_mk ρ τ U hτ b v

include hτ in
/-- A vanishing original Jacquet quotient remains zero after scalar extension. -/
theorem subsingleton_scalarExtension
    [Subsingleton (Coinvariants ρ U 1)] : Subsingleton (Coinvariants τ U 1) :=
  (scalarExtensionEquiv ρ τ U hτ).injective.subsingleton

end Langlands.Jacquet.Localization
