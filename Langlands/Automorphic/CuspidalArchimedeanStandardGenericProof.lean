import Langlands.Automorphic.ArchimedeanPlaceParameterNontrivial
import Langlands.Automorphic.CuspidalArchimedeanComponentUnitaryProof
import Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker

/-!
# Generic archimedean standard-module components

The image of a place parameter is nonzero and stable under the compact and Lie actions.
The Whittaker functional on that image pulls back to the standard module.
-/

noncomputable section

universe u

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open OperatorRealization

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Stability under the actions of `1 ⊗ m` implies stability under the complexified action. -/
private theorem mem_of_one_tmul {M V : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup V]
    [Module ℂ V] (φ : (ℂ ⊗[ℝ] M) →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (h : ∀ m : M, ∀ x ∈ W, φ (1 ⊗ₜ m) x ∈ W) : ∀ X : ℂ ⊗[ℝ] M, ∀ x ∈ W, φ X x ∈ W := by
  intro X
  induction X using TensorProduct.inductionOn with
  | tmul c m =>
    intro x hx
    have hcm : (c ⊗ₜ[ℝ] m : ℂ ⊗[ℝ] M) = c • ((1 : ℂ) ⊗ₜ m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcm, map_smul, LinearMap.smul_apply]
    exact W.smul_mem c (h m x hx)
  | add X Y hX hY =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hX x hx) (hY x hx)

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance standardGenericRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance standardGenericContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance standardGenericSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance standardGenericFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance standardGenericStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance standardGenericSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 400000 in
/-- The standard module of a real place parameter of a cuspidal realization is generic. -/
theorem isRealGeneric_of_hasRealPlaceParameter {r : ℕ} (T : CuspidalOperatorRealization F r)
    {v : RP} {ds : List RealBlock} (h : T.realization.HasRealPlaceParameter v ds) :
    Archimedean.IsRealGenericGKModule (r + 1) (Archimedean.realStandardLie (r + 1) ds) := by
  obtain ⟨hrank, A, hA, hK, hL⟩ := h
  have : Nontrivial (realStandardKFinite (r + 1) ds) :=
    Submodule.nontrivial_iff_ne_bot.mpr (realStandardKFinite_ne_bot _ _ hrank)
  have hrange : LinearMap.range A ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp (LinearEquiv.ofInjective A hA).injective.nontrivial
  have hstable : PlaceComponent.IsStable (T.realization.realPlaceCompactRepresentation v)
      (T.realization.realPlaceLieAction v) (LinearMap.range A) := by
    constructor
    · rintro k _ ⟨f, rfl⟩
      exact ⟨_, realPlaceParameter_compact hK k f⟩
    · refine mem_of_one_tmul (T.realization.realPlaceLieAction v).toLinearMap
        (LinearMap.range A) ?_
      rintro X _ ⟨f, rfl⟩
      exact ⟨_, realPlaceParameter_lie hL X f⟩
  obtain ⟨a, ha, ℓ, ⟨x, hx, hℓx⟩, hW⟩ :=
    (cuspidalArchimedeanWhittakerFunctional F r T.realization T.cuspidal).1 v _ hrange hstable
  refine ⟨ℓ ∘ₗ A, ?_, a, ha, fun X hX f => ?_⟩
  · obtain ⟨f, rfl⟩ := hx
    intro hzero
    exact hℓx (LinearMap.congr_fun hzero f)
  · simp only [LinearMap.comp_apply]
    rw [realPlaceParameter_lie hL X f]
    exact hW X hX (A f) ⟨f, rfl⟩

set_option maxHeartbeats 400000 in
/-- The standard module of a complex place parameter of a cuspidal realization is generic. -/
theorem isComplexGeneric_of_hasComplexPlaceParameter {r : ℕ} (T : CuspidalOperatorRealization F r)
    {v : CP} {ds : List ComplexCharacterData} (h : T.realization.HasComplexPlaceParameter v ds) :
    Archimedean.IsComplexGenericGKModule (r + 1) (Archimedean.complexStandardLie (r + 1) ds) := by
  obtain ⟨hlen, A, hA, hK, hL⟩ := h
  have : Nontrivial (complexStandardKFinite (r + 1) ds) :=
    Submodule.nontrivial_iff_ne_bot.mpr (complexStandardKFinite_ne_bot _ _ hlen)
  have hrange : LinearMap.range A ≠ ⊥ :=
    Submodule.nontrivial_iff_ne_bot.mp (LinearEquiv.ofInjective A hA).injective.nontrivial
  have hstable : PlaceComponent.IsStable (T.realization.complexPlaceCompactRepresentation v)
      (T.realization.complexPlaceLieAction v) (LinearMap.range A) := by
    constructor
    · rintro k _ ⟨f, rfl⟩
      exact ⟨_, complexPlaceParameter_compact hK k f⟩
    · refine mem_of_one_tmul (T.realization.complexPlaceLieAction v).toLinearMap
        (LinearMap.range A) ?_
      rintro X _ ⟨f, rfl⟩
      exact ⟨_, complexPlaceParameter_lie hL X f⟩
  obtain ⟨a, ha, ℓ, ⟨x, hx, hℓx⟩, hW⟩ :=
    (cuspidalArchimedeanWhittakerFunctional F r T.realization T.cuspidal).2 v _ hrange hstable
  refine ⟨ℓ ∘ₗ A, ?_, a, ha, fun X hX f => ?_⟩
  · obtain ⟨f, rfl⟩ := hx
    intro hzero
    exact hℓx (LinearMap.congr_fun hzero f)
  · simp only [LinearMap.comp_apply]
    rw [complexPlaceParameter_lie hL X f]
    exact hW X hX (A f) ⟨f, rfl⟩

/-- The archimedean standard-module components of a cuspidal realization are generic. -/
theorem cuspidalArchimedeanStandardGeneric : CuspidalArchimedeanStandardGenericStatement.{u} :=
  fun _ _ _ _ _ T => ⟨fun _ _ h => isRealGeneric_of_hasRealPlaceParameter T h,
    fun _ _ h => isComplexGeneric_of_hasComplexPlaceParameter T h⟩

end Langlands.Automorphic
