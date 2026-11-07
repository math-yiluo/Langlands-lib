import Langlands.Automorphic.ConstantUnitaryForm
import Langlands.Automorphic.ConstantRealizationProperties
import Langlands.Automorphic.TensorPresentation
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Representation.RestrictedTensor.Scalars
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Mathlib.Algebra.Module.ULift

/-! # Genuine tensor presentations of the actual constant line -/

noncomputable section
open scoped Classical TensorProduct

universe uF uP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ConstantFunctions

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (realization F n).Space := Submodule.addCommGroup _

/-- A local constant scalar line in the independently chosen factor universe. -/
def tensorLocalModel (v : FinitePlace F) :
    Representation ℂ (FiniteLocalGL F n v) (ULift.{uP} ℂ) :=
  Representation.trivial ℂ _ _

theorem tensorLocalModel_isSmooth (v : FinitePlace F) :
    Langlands.IsSmooth (tensorLocalModel.{uF, uP} F n v) :=
  fun _ => ⟨⊤, fun _ => rfl⟩

theorem liftedScalar_finrank :
    Module.finrank ℂ (ULift.{uP} ℂ) = 1 := by
  rw [(ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).finrank_eq]
  exact Module.finrank_self ℂ

theorem tensorLocalModel_isIrreducible (v : FinitePlace F) :
    (tensorLocalModel.{uF, uP} F n v).IsIrreducible :=
  Langlands.ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one
    (Langlands.SmoothRep.of _ (tensorLocalModel_isSmooth.{uF, uP} F n v))
    liftedScalar_finrank

theorem tensorLocalModel_isAdmissible (v : FinitePlace F) :
    Langlands.IsAdmissible (tensorLocalModel.{uF, uP} F n v) := by
  let : FiniteDimensional ℂ (ULift.{uP} ℂ) :=
    FiniteDimensional.of_injective
      (ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
      (ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).injective
  exact ⟨tensorLocalModel_isSmooth F n v, fun _ => inferInstance⟩

/-- Every local group fixes the lifted scalar-one reference. -/
theorem tensorReference_fixed (v : FinitePlace F)
    (_hv : v ∉ (∅ : Finset (FinitePlace F)))
    (g : FiniteLocalGL F n v) (_hg : g ∈ localIntegral F n v) :
    tensorLocalModel.{uF, uP} F n v g (ULift.up 1) = ULift.up 1 := rfl

/-- Factorwise descent and multiplication evaluate the genuine lifted tensor. -/
def tensorScalarEquiv :
    Space ℂ (fun _ : FinitePlace F => ULift.{uP} ℂ) ∅ (fun _ => ULift.up 1) ≃ₗ[ℂ] ℂ :=
  (Langlands.RestrictedTensor.congr ∅ ∅ (fun _ => ULift.up 1) (fun _ => (1 : ℂ))
    (fun _ => ULift.moduleEquiv)
    (Filter.Eventually.of_forall fun _ => rfl)).trans
      (Langlands.RestrictedTensor.scalarEquiv ℂ ∅)

omit [NumberField F] in
@[simp]
theorem tensorScalarEquiv_pure
    (S : Index (∅ : Finset (FinitePlace F))) (x : S.1 → ULift.{uP} ℂ) :
    tensorScalarEquiv F (pure ∅ (fun _ => ULift.up 1) S x) = ∏ v, (x v).down := by
  change Langlands.RestrictedTensor.scalarEquiv ℂ ∅
    (Langlands.RestrictedTensor.map ∅ ∅ (fun _ => ULift.up 1) (fun _ => (1 : ℂ))
      (fun _ => (ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).toLinearMap)
      (Filter.Eventually.of_forall fun _ => rfl)
      (pure ∅ (fun _ => ULift.up 1) S x)) = _
  rw [Langlands.RestrictedTensor.map_pure_of_preserves ∅ ∅
    (fun _ : FinitePlace F => (ULift.up 1 : ULift.{uP} ℂ)) (fun _ => (1 : ℂ))
    (fun _ => (ULift.moduleEquiv : ULift.{uP} ℂ ≃ₗ[ℂ] ℂ).toLinearMap)
    (Filter.Eventually.of_forall fun _ => rfl) S
    (Finset.empty_subset _) (fun _ _ => rfl),
    Langlands.RestrictedTensor.scalarEquiv_pure]
  rfl

/-- The restricted tensor action on constant lines is itself trivial. -/
def finiteTensorScalarEquiv :
    (tensorRepresentation F n (tensorLocalModel.{uF, uP} F n)
      ∅ (fun _ => ULift.up 1) (tensorReference_fixed F n)).Equiv
        (Representation.trivial ℂ (FiniteAdelicGL F n) ℂ) :=
  Representation.Equiv.mk (tensorScalarEquiv.{uF, uP} F) (fun _g => by
    change (tensorScalarEquiv.{uF, uP} F).toLinearMap.comp
        (Langlands.RestrictedTensor.map ∅ ∅ (fun _ => ULift.up 1) (fun _ => ULift.up 1)
          (fun _ => LinearMap.id) _) =
      LinearMap.id.comp (tensorScalarEquiv.{uF, uP} F).toLinearMap
    rw [Langlands.RestrictedTensor.map_id]
    rfl)

/-- This equivalence has the actual finite constant form space as codomain. -/
def finiteFormEquiv :
    (Representation.trivial ℂ (FiniteAdelicGL F n) ℂ).Equiv
      (realization F n).toFiniteRealization.representation :=
  (scalarFiniteEquiv F n).trans (realization F n).finiteEquiv

/-- An actual restricted tensor presentation in every independent factor universe. -/
def finiteTensorPresentation :
    FiniteTensorPresentation F n (tensorLocalModel.{uF, uP} F n)
      ∅ (fun _ => ULift.up 1) (tensorReference_fixed F n)
      (realization F n).toFiniteRealization where
  reference_nonzero _ _ := fun h => one_ne_zero (congrArg ULift.down h)
  equiv := (finiteTensorScalarEquiv F n).trans (finiteFormEquiv F n)

/-- The tensor map covers precisely the actual constant line. -/
theorem finiteTensorPresentation_image :
    finiteRealizationImage F n (finiteTensorPresentation.{uF, uP} F n).toMap =
      (realization F n).toFiniteRealization :=
  (finiteTensorPresentation F n).image_toMap

theorem finiteTensorPresentation_injective :
    Function.Injective (finiteTensorPresentation.{uF, uP} F n).toMap :=
  (finiteTensorPresentation F n).toMap_injective

@[simp]
theorem finiteTensorPresentation_toMap_pure
    (S : Index (∅ : Finset (FinitePlace F))) (x : S.1 → ULift.{uP} ℂ) :
    (finiteTensorPresentation F n).toMap (pure ∅ (fun _ => ULift.up 1) S x) =
      form F n (∏ v, (x v).down) := by
  change form F n (tensorScalarEquiv F (pure ∅ (fun _ => ULift.up 1) S x)) = _
  rw [tensorScalarEquiv_pure]

/-- The elementary tensors map to the literal constant automorphic functions. -/
theorem evaluate_finiteTensorPresentation_pure
    (S : Index (∅ : Finset (FinitePlace F))) (x : S.1 → ULift.{uP} ℂ)
    (a : AdelicGL F n) :
    ContinuousRationalFunctions.evaluate F n
      (automorphicToContinuous F n
        ((finiteTensorPresentation F n).toMap (pure ∅ (fun _ => ULift.up 1) S x))) a =
      ∏ v, (x v).down := by
  rw [finiteTensorPresentation_toMap_pure, evaluate_form]

end Langlands.Automorphic.ConstantFunctions
