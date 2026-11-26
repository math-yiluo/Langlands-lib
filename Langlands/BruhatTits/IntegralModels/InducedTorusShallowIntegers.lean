import Langlands.Geometry.FormalGroup.CompletedUnramifiedCoefficients
import Langlands.BruhatTits.IntegralModels.ConnectedImage.Integers
import Langlands.LocalField.AlgebraicExtensionValuation
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Integral coefficient algebras and normalized depth ideals -/

noncomputable section

universe u

open Langlands.GroupScheme Langlands.LocalGalois Langlands.LocalGalois.Separable
open Langlands.Geometry.Building Langlands.LocalField
open scoped NNReal TensorProduct nonZeroDivisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels.InducedTorusShallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F (SeparableClosure F)

theorem geometricValue_nonneg_iff (x : Ω) : (0 : WithTop ℝ) ≤ ν x ↔ sepClosureValuation F x ≤ 1 := by
  have h := logAdditiveValuation_le_iff (sepClosureValuation F) (localLogScale F)
    (localLogScale_pos F) 1 x
  change ν 1 ≤ ν x ↔ _ at h
  simpa only [AddValuation.map_one, map_one] using h

/-- The order-one uniformizer of the local field, viewed as an integral scalar
in the maximal unramified field. -/
def baseUniformizer : O := by
  refine ⟨algebraMap F K (LocalField.uniformizer F), ?_⟩
  change sepClosureValuation F (algebraMap F Ω (LocalField.uniformizer F)) ≤ 1
  apply (geometricValue_nonneg_iff F _).mp
  rw [algebraicExtensionAddValuation_base_of_ord_eq F Ω (ord_uniformizer F)]
  norm_num

theorem baseUniformizer_ne_zero : baseUniformizer F ≠ 0 := by
  intro h
  have hz : algebraMap F K (LocalField.uniformizer F) = 0 := congrArg Subtype.val h
  exact (map_ne_zero_iff _ (algebraMap F K).injective).2 (LocalField.uniformizer_ne_zero F) hz

theorem baseUniformizer_value : ν (((baseUniformizer F : O) : K) : Ω) = 1 := by
  change ν (algebraMap F Ω (LocalField.uniformizer F)) = 1
  simpa using algebraicExtensionAddValuation_base_of_ord_eq F Ω (ord_uniformizer F)

section Factors

variable (L : IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [FiniteDimensional (inertiaFixedField F) L]

local notation "Oₗ" => ConnectedImage.integers F L

private local instance integersFieldAlgebra : Algebra O L :=
  ((algebraMap K L).comp (algebraMap O K)).toAlgebra

private local instance integersFieldTower : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq' rfl
private local instance integersCoefficientTower : IsScalarTower O Oₗ L := IsScalarTower.of_algebraMap_eq' rfl

/-- Separability of the embedded field is sufficient for finiteness of its
valuation ring over the maximal unramified integers. -/
instance factorIntegers_finite : Module.Finite O Oₗ :=
  IsIntegralClosure.finite O K L Oₗ

instance factorIntegers_free : Module.Free O Oₗ := by
  have : Module.IsTorsionFree O L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr <| by
      change Function.Injective ((algebraMap K L).comp (algebraMap O K))
      exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  exact IsIntegralClosure.module_free O K L Oₗ

private local instance factorIntegers_isPushout : Algebra.IsPushout O K Oₗ L := by
  have : IsLocalization (Algebra.algebraMapSubmonoid Oₗ O⁰) L :=
    IsIntegralClosure.isLocalization O K L Oₗ
  exact (Algebra.isPushout_of_isLocalization (R := O) (A := K) O⁰ Oₗ L).symm

/-- Recover the coefficient field by inverting the nonzero scalars in the
maximal unramified integers. -/
def factorTensorEquiv : K ⊗[O] Oₗ ≃ₐ[K] L := Algebra.IsPushout.equiv O K Oₗ L

omit [FiniteDimensional (inertiaFixedField F) L] in
theorem factorTensorEquiv_tmul (a : K) (b : Oₗ) :
    factorTensorEquiv F L (a ⊗ₜ b) = algebraMap K L a * (b : L) :=
  Algebra.IsPushout.equiv_tmul O K Oₗ L a b

end Factors

section Products

variable {I : Type u} [Fintype I] (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [∀ i, FiniteDimensional (inertiaFixedField F) (E i)]

/-- The finite product of the valuation rings in the coefficient fields. -/
abbrev productIntegers := ∀ i, ConnectedImage.integers F (E i)

local notation "C" => productIntegers F E
local notation "B" => (∀ i, E i)
private local instance integerFactorFieldAlgebra : ∀ i, Algebra K (E i) := fun i => (E i).toSubalgebra.algebra
private local instance integerFactorFieldModule : ∀ i, Module K (E i) := fun i =>
  @Algebra.toModule _ _ _ _ (E i).toSubalgebra.algebra
private local instance integerFactorFieldSMul : ∀ i, SMul K (E i) := fun i => (E i).toSubalgebra.algebra.toSMul
private local instance fieldProductAlgebra : Algebra K B := Pi.algebra _ _
private local instance integerFieldProductModule : Module K B := @Algebra.toModule _ _ _ _ (fieldProductAlgebra F E)
private local instance integerFieldProductSMul : SMul K B := (fieldProductAlgebra F E).toSMul

instance productIntegers_algebra : Algebra O C := Pi.algebra _ _
instance productIntegers_finite : Module.Finite O C := Module.Finite.pi
instance productIntegers_free : Module.Free O C := Module.Free.pi O (fun i => ConnectedImage.integers F (E i))

/-- The generic coefficient comparison is the product of the individual
fraction-field identifications. -/
def productTensorEquiv : K ⊗[O] C ≃ₐ[K] B := by
  classical
  exact (Algebra.TensorProduct.piRight O K K (fun i => ConnectedImage.integers F (E i))).trans
    (AlgEquiv.piCongrRight (fun i => factorTensorEquiv F (E i)))

omit [∀ i, FiniteDimensional (inertiaFixedField F) (E i)] in
theorem productTensorEquiv_tmul (a : K) (b : C) (i : I) :
    productTensorEquiv F E (a ⊗ₜ b) i = algebraMap K (E i) a * (b i : E i) := by
  simp [productTensorEquiv, factorTensorEquiv_tmul]

/-- The ideal of integral tuples whose coordinates have normalized additive
value at least `r`. -/
def depthIdeal (r : ℝ≥0) : Ideal C where
  carrier := {b | ∀ i, ((r : ℝ) : WithTop ℝ) ≤ ν (((b i : ConnectedImage.integers F (E i)) : E i) : Ω)}
  zero_mem' i := by simp
  add_mem' ha hb i := by
    change ((r : ℝ) : WithTop ℝ) ≤ ν (_ + _)
    exact (le_min (ha i) (hb i)).trans (AddValuation.map_add ν _ _)
  smul_mem' a b hb := by
    intro i
    change ((r : ℝ) : WithTop ℝ) ≤ ν (_ * _)
    rw [AddValuation.map_mul]
    have ha : (0 : WithTop ℝ) ≤ ν (((a i : ConnectedImage.integers F (E i)) : E i) : Ω) :=
      (geometricValue_nonneg_iff F _).mpr (a i).property
    exact (hb i).trans (le_add_of_nonneg_left ha)

omit [Fintype I] [∀ i, FiniteDimensional (inertiaFixedField F) (E i)] in
theorem mem_depthIdeal (r : ℝ≥0) (b : C) :
    b ∈ depthIdeal F E r ↔ ∀ i, ((r : ℝ) : WithTop ℝ) ≤ ν ((b i : E i) : Ω) := Iff.rfl

omit [Fintype I] [∀ i, FiniteDimensional (inertiaFixedField F) (E i)] in
/-- In shallow depth the ideal contains the image of a nonzero base scalar. -/
theorem baseUniformizer_mem_depthIdeal (r : ℝ≥0) (hr : r < 1) :
    algebraMap O C (baseUniformizer F) ∈ depthIdeal F E r := by
  rw [mem_depthIdeal]
  intro i
  change ((r : ℝ) : WithTop ℝ) ≤ ν (((baseUniformizer F : O) : K) : Ω)
  rw [baseUniformizer_value]
  exact_mod_cast hr.le

end Products
end Langlands.BruhatTits.IntegralModels.InducedTorusShallow
