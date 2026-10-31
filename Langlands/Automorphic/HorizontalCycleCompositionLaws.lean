import Langlands.Automorphic.HorizontalCohomologyTransport

/-! # Composition of actual horizontal cycle transport -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 1000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance horizontalCycleCompositionLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T U : OperatorRealization F n)

local instance horizontalCycleCompositionLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance horizontalCycleCompositionLawsThirdGroup : AddCommGroup U.Space :=
  Submodule.addCommGroup _


namespace Intertwiner

variable {S T U}

/-- Actual operator composition acts by successive cycle transport. -/
abbrev horizontalCyclesMap_comp_apply (A : S.Intertwiner T) (B : T.Intertwiner U)
    (q : ℕ) (f : S.horizontalCycles q) :
    horizontalCyclesMap (S := S) (T := U) (B.comp A) q f =
      horizontalCyclesMap (S := T) (T := U) B q
        (horizontalCyclesMap (S := S) (T := T) A q f) := by
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Restriction to cycles preserves composition of the actual full maps. -/
abbrev horizontalCyclesMap_comp (A : S.Intertwiner T) (B : T.Intertwiner U) (q : ℕ) :
    horizontalCyclesMap (S := S) (T := U) (B.comp A) q =
      (horizontalCyclesMap (S := T) (T := U) B q).comp
        (horizontalCyclesMap (S := S) (T := T) A q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact horizontalCyclesMap_comp_apply (S := S) (T := T) (U := U) A B q

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
