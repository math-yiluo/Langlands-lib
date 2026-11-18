import Langlands.Geometry.FormalGroup.DivisionOrder
import Langlands.Algebra.LocalDivisionIntegerLattice
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Scalar extension of the original local division order -/

noncomputable section

universe u

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision TensorProduct
open scoped nonZeroDivisors

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : Algebra 𝒪[K] D := Algebra.compHom D (algebraMap 𝒪[K] K)
local instance : IsScalarTower 𝒪[K] K D := .of_algebraMap_smul (fun _ _ => rfl)

private def integerInclusion : IntegerRing K D →ₐ[𝒪[K]] D where
  toRingHom := (localReducedNormValuation K D).integer.subtype
  commutes' := coe_algebraMap K D

private def integerTensorMap : K ⊗[𝒪[K]] IntegerRing K D →ₐ[K] D :=
  AlgHom.liftEquiv _ _ _ _ (integerInclusion K D)

private theorem integerTensorMap_bijective : Function.Bijective (integerTensorMap K D) := by
  have : IsFractionRing 𝒪[K] K := (Valuation.integer.integers (valuation K)).isFractionRing
  have : Module.Flat 𝒪[K] K := IsLocalization.flat K (𝒪[K]⁰)
  let j := (integerInclusion K D).toLinearMap
  have hId : IsLocalizedModule (𝒪[K]⁰) (LinearMap.id : D →ₗ[𝒪[K]] D) :=
    isLocalizedModule_id _ D K
  let e := (IsLocalizedModule.isBaseChange (𝒪[K]⁰) K (LinearMap.id : D →ₗ[𝒪[K]] D)).equiv
  have hfactor : (integerTensorMap K D).toLinearMap = e.toLinearMap.comp (j.baseChange K) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro k a
    change k • (a : D) = e (k ⊗ₜ[𝒪[K]] (a : D))
    rw [IsBaseChange.equiv_tmul, LinearMap.id_apply]
  refine ⟨?_, ?_⟩
  · change Function.Injective (integerTensorMap K D).toLinearMap
    rw [hfactor]
    exact e.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap j Subtype.val_injective)
  · change Function.Surjective (j.liftBaseChange K)
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
    change Submodule.span K (Set.range ((↑) : IntegerRing K D → D)) = ⊤
    have hrange : Set.range ((↑) : IntegerRing K D → D) =
        (localDivisionIntegerLattice K D : Set D) := by
      ext x
      exact ⟨fun ⟨a, h⟩ => h ▸ a.prop, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    rw [hrange, localDivisionIntegerLattice_span]

/-- The original integer order recovers the original division algebra after adjoining base fractions. -/
def integerTensorEquiv : K ⊗[𝒪[K]] IntegerRing K D ≃ₐ[K] D :=
  AlgEquiv.ofBijective (integerTensorMap K D) (integerTensorMap_bijective K D)

@[simp]
theorem integerTensorEquiv_tmul (k : K) (a : IntegerRing K D) :
    integerTensorEquiv K D (k ⊗ₜ[𝒪[K]] a) = k • (a : D) := rfl

@[simp]
theorem integerTensorEquiv_symm_coe (a : IntegerRing K D) :
    (integerTensorEquiv K D).symm (a : D) = 1 ⊗ₜ[𝒪[K]] a := by
  apply (integerTensorEquiv K D).injective
  rw [AlgEquiv.apply_symm_apply, integerTensorEquiv_tmul, one_smul]

end Langlands.FormalGroup.LocalDivision
