import Langlands.Automorphic.HorizontalCohomologyTransport

/-! # Actual horizontal cycle transport formulas and identity -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000
set_option synthInstance.maxHeartbeats 1000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance horizontalCycleTransportLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleTransportLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleTransportLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCycleTransportLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCycleTransportLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalCycleTransportLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalCycleTransportLawsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _


namespace Intertwiner

variable {S T}

/-- The actual cycle map retains the same transported cochain. -/
abbrev horizontalCyclesMap_val (A : S.Intertwiner T) (q : ℕ)
    (f : S.horizontalCycles q) :
    (horizontalCyclesMap (S := S) (T := T) A q f).val =
      horizontalMap (S := S) (T := T) A q f.val := rfl

/-- At each Lie tuple, transport applies the same full operator map. -/
abbrev horizontalCyclesMap_apply (A : S.Intertwiner T) (q : ℕ)
    (f : S.horizontalCycles q) (X : Fin q → ReducedComplexLieAlgebra F n) :
    (horizontalCyclesMap (S := S) (T := T) A q f).val.val X = A (f.val.val X) := rfl


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000 in
/-- Full operator identity induces identity on the actual cycle representation. -/
abbrev horizontalCyclesMap_id (q : ℕ) :
    horizontalCyclesMap (S := S) (T := S)
        (Representation.IntertwiningMap.id S.representation) q =
      Representation.IntertwiningMap.id (S.horizontalCyclesFiniteRepresentation q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl


end Intertwiner
end OperatorRealization
end Langlands.Automorphic
