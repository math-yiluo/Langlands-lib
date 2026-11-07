import Langlands.Automorphic.PlaceEnvelopingAction
import Langlands.Global.ArchimedeanPlaceEnvelopingTensor

/-! # Actual two-place enveloping tensor actions on original automorphic vectors -/

noncomputable section
universe u

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

local instance placeEnvelopingTensorRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeEnvelopingTensorStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance placeEnvelopingTensorSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance placeEnvelopingTensorTargetAddCommGroup : AddCommGroup T.Space := Submodule.addCommGroup _

/-- Actual local enveloping operators commute at distinct real places. -/
theorem realPlaceEnvelopingActions_commute (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    Commute (S.realPlaceEnvelopingAction v a) (S.realPlaceEnvelopingAction w b) := by
  change S.envelopingAction (realPlaceEnvelopingInclusion F n v a) *
      S.envelopingAction (realPlaceEnvelopingInclusion F n w b) =
    S.envelopingAction (realPlaceEnvelopingInclusion F n w b) *
      S.envelopingAction (realPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg S.envelopingAction
    (realPlaceEnvelopingInclusions_commute F n v w h a b).eq

theorem complexPlaceEnvelopingActions_commute (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (S.complexPlaceEnvelopingAction v a) (S.complexPlaceEnvelopingAction w b) := by
  change S.envelopingAction (complexPlaceEnvelopingInclusion F n v a) *
      S.envelopingAction (complexPlaceEnvelopingInclusion F n w b) =
    S.envelopingAction (complexPlaceEnvelopingInclusion F n w b) *
      S.envelopingAction (complexPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg S.envelopingAction
    (complexPlaceEnvelopingInclusions_commute F n v w h a b).eq

theorem realComplexPlaceEnvelopingActions_commute (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    Commute (S.realPlaceEnvelopingAction v a) (S.complexPlaceEnvelopingAction w b) := by
  change S.envelopingAction (realPlaceEnvelopingInclusion F n v a) *
      S.envelopingAction (complexPlaceEnvelopingInclusion F n w b) =
    S.envelopingAction (complexPlaceEnvelopingInclusion F n w b) *
      S.envelopingAction (realPlaceEnvelopingInclusion F n v a)
  simpa only [map_mul] using congrArg S.envelopingAction
    (realComplexPlaceEnvelopingInclusions_commute F n v w a b).eq

/-- The actual two-real-place algebra tensor product acts on the original carrier. -/
def realPlacesEnvelopingTensorAction (v w : RP) (h : v ≠ w) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ S.Space :=
  S.envelopingAction.comp (realPlacesEnvelopingTensorMap F n v w h)

def complexPlacesEnvelopingTensorAction (v w : CP) (h : v ≠ w) :
    (ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ S.Space :=
  S.envelopingAction.comp (complexPlacesEnvelopingTensorMap F n v w h)

def realComplexPlacesEnvelopingTensorAction (v : RP) (w : CP) :
    (RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) →ₐ[ℂ]
      Module.End ℂ S.Space :=
  S.envelopingAction.comp (realComplexPlacesEnvelopingTensorMap F n v w)

/-- Pure tensors act by composition of the two original place differential operators. -/
theorem realPlacesEnvelopingTensorAction_tmul (v w : RP) (h : v ≠ w)
    (a b : RealPlaceEnvelopingAlgebra n) :
    S.realPlacesEnvelopingTensorAction v w h (a ⊗ₜ[ℂ] b) =
      S.realPlaceEnvelopingAction v a * S.realPlaceEnvelopingAction w b := by
  exact (congrArg S.envelopingAction
    (realPlacesEnvelopingTensorMap_tmul F n v w h a b)).trans
      (S.envelopingAction.map_mul _ _)

theorem complexPlacesEnvelopingTensorAction_tmul (v w : CP) (h : v ≠ w)
    (a b : ComplexPlaceEnvelopingAlgebra n) :
    S.complexPlacesEnvelopingTensorAction v w h (a ⊗ₜ[ℂ] b) =
      S.complexPlaceEnvelopingAction v a * S.complexPlaceEnvelopingAction w b := by
  exact (congrArg S.envelopingAction
    (complexPlacesEnvelopingTensorMap_tmul F n v w h a b)).trans
      (S.envelopingAction.map_mul _ _)

theorem realComplexPlacesEnvelopingTensorAction_tmul (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n) (b : ComplexPlaceEnvelopingAlgebra n) :
    S.realComplexPlacesEnvelopingTensorAction v w (a ⊗ₜ[ℂ] b) =
      S.realPlaceEnvelopingAction v a * S.complexPlaceEnvelopingAction w b := by
  exact (congrArg S.envelopingAction
    (realComplexPlacesEnvelopingTensorMap_tmul F n v w a b)).trans
      (S.envelopingAction.map_mul _ _)

theorem inclusion_realPlacesEnvelopingTensorAction (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.inclusion (S.realPlacesEnvelopingTensorAction v w h a f) =
      stableAutomorphicEnvelopingAction F n (realPlacesEnvelopingTensorMap F n v w h a)
        (S.inclusion f) := rfl

theorem inclusion_complexPlacesEnvelopingTensorAction (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.inclusion (S.complexPlacesEnvelopingTensorAction v w h a f) =
      stableAutomorphicEnvelopingAction F n (complexPlacesEnvelopingTensorMap F n v w h a)
        (S.inclusion f) := rfl

theorem inclusion_realComplexPlacesEnvelopingTensorAction (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.inclusion (S.realComplexPlacesEnvelopingTensorAction v w a f) =
      stableAutomorphicEnvelopingAction F n (realComplexPlacesEnvelopingTensorMap F n v w a)
        (S.inclusion f) := rfl

theorem finiteRepresentation_realPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.finiteRepresentation d (S.realPlacesEnvelopingTensorAction v w h a f) =
      S.realPlacesEnvelopingTensorAction v w h a (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (realPlacesEnvelopingTensorMap F n v w h a) f

theorem finiteRepresentation_complexPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.finiteRepresentation d (S.complexPlacesEnvelopingTensorAction v w h a f) =
      S.complexPlacesEnvelopingTensorAction v w h a (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (complexPlacesEnvelopingTensorMap F n v w h a) f

theorem finiteRepresentation_realComplexPlacesEnvelopingTensorAction
    (d : FiniteAdelicGL F n) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.finiteRepresentation d (S.realComplexPlacesEnvelopingTensorAction v w a f) =
      S.realComplexPlacesEnvelopingTensorAction v w a (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (realComplexPlacesEnvelopingTensorMap F n v w a) f

namespace Intertwiner

variable {S T}

/-- Every original full intertwiner retains the action of every two-place algebra element. -/
theorem realPlacesEnvelopingTensorAction (A : S.Intertwiner T) (v w : RP) (h : v ≠ w)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    A (S.realPlacesEnvelopingTensorAction v w h a f) =
      T.realPlacesEnvelopingTensorAction v w h a (A f) :=
  A.differential (realPlacesEnvelopingTensorMap F n v w h a) f

theorem complexPlacesEnvelopingTensorAction (A : S.Intertwiner T) (v w : CP) (h : v ≠ w)
    (a : ComplexPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    A (S.complexPlacesEnvelopingTensorAction v w h a f) =
      T.complexPlacesEnvelopingTensorAction v w h a (A f) :=
  A.differential (complexPlacesEnvelopingTensorMap F n v w h a) f

theorem realComplexPlacesEnvelopingTensorAction (A : S.Intertwiner T) (v : RP) (w : CP)
    (a : RealPlaceEnvelopingAlgebra n ⊗[ℂ] ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    A (S.realComplexPlacesEnvelopingTensorAction v w a f) =
      T.realComplexPlacesEnvelopingTensorAction v w a (A f) :=
  A.differential (realComplexPlacesEnvelopingTensorMap F n v w a) f

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
