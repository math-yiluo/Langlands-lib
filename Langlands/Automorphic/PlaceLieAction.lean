import Langlands.Automorphic.OperatorLieAction
import Langlands.Global.ArchimedeanPlaceLie

/-! # Per-place restrictions of the actual automorphic differential action -/

noncomputable section

universe u

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL NumberField

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance placeLieRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeLieContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeLieSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeLieFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeLieStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance placeLieSpaceAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance placeLieTargetAddCommGroup : AddCommGroup T.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Restrict the genuine differential to the complexified real-place matrix Lie algebra. -/
def realPlaceLieAction (v : RP) : (ℂ ⊗[ℝ] RM) →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.complexLieAction.comp (realPlaceComplexLieInclusion F n v)

/-- Restrict to a complex place, complexifying its entire underlying real matrix Lie algebra. -/
def complexPlaceLieAction (v : CP) : (ℂ ⊗[ℝ] CM) →ₗ⁅ℂ⁆ Module.End ℂ S.Space :=
  S.complexLieAction.comp (complexPlaceComplexLieInclusion F n v)

theorem realPlaceLieAction_apply (v : RP) (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.realPlaceLieAction v X f =
      S.envelopingAction (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) f :=
  rfl

theorem complexPlaceLieAction_apply (v : CP) (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.complexPlaceLieAction v X f =
      S.envelopingAction
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) f := rfl

/-- The local operator remains the original differential on the embedded actual functions. -/
theorem inclusion_realPlaceLieAction (v : RP) (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.inclusion (S.realPlaceLieAction v X f) =
      stableAutomorphicEnvelopingAction F n
        (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X))
          (S.inclusion f) := rfl

theorem inclusion_complexPlaceLieAction (v : CP) (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.inclusion (S.complexPlaceLieAction v X f) =
      stableAutomorphicEnvelopingAction F n
        (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X))
          (S.inclusion f) := rfl

theorem finiteRepresentation_realPlaceLieAction (d : FiniteAdelicGL F n)
    (v : RP) (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    S.finiteRepresentation d (S.realPlaceLieAction v X f) =
      S.realPlaceLieAction v X (S.finiteRepresentation d f) :=
  S.finiteRepresentation_complexLieAction d (realPlaceComplexLieInclusion F n v X) f

theorem finiteRepresentation_complexPlaceLieAction (d : FiniteAdelicGL F n)
    (v : CP) (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    S.finiteRepresentation d (S.complexPlaceLieAction v X f) =
      S.complexPlaceLieAction v X (S.finiteRepresentation d f) :=
  S.finiteRepresentation_complexLieAction d (complexPlaceComplexLieInclusion F n v X) f

/-- The actual global differential on every real generator is the sum of the place operators. -/
theorem complexify_action_eq_sum_place (X : RealLieAlgebra F n) (f : S.Space) :
    S.complexLieAction (complexify F n X) f =
      (∑ v : RP, S.realPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X) f) +
      (∑ v : CP, S.complexPlaceLieAction v
        ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X) f) := by
  have h := congrArg (fun Y : RealLieAlgebra F n =>
    S.complexLieAction (complexify F n Y) f) (sum_placeLieInclusions F n X).symm
  simpa only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
    realPlaceLieAction, complexPlaceLieAction, LieHom.comp_apply,
    realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul,
    complexify_apply] using h

namespace Intertwiner

variable {S T}

/-- A full automorphic intertwiner retains every actual real-place differential operator. -/
theorem realPlaceLieAction (A : S.Intertwiner T) (v : RP)
    (X : ℂ ⊗[ℝ] RM) (f : S.Space) :
    A (S.realPlaceLieAction v X f) = T.realPlaceLieAction v X (A f) :=
  A.differential (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) f

/-- The same original intertwiner retains both real directions at every complex place. -/
theorem complexPlaceLieAction (A : S.Intertwiner T) (v : CP)
    (X : ℂ ⊗[ℝ] CM) (f : S.Space) :
    A (S.complexPlaceLieAction v X f) = T.complexPlaceLieAction v X (A f) :=
  A.differential (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) f

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
