import Langlands.Automorphic.HorizontalCohomologyTransport

/-! # Underlying linear maps of actual horizontal transport -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance horizontalLinearMapsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalLinearMapsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalLinearMapsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalLinearMapsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalLinearMapsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalLinearMapsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalLinearMapsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "ρ" => S.compactRepresentation
local notation "τ" => T.compactRepresentation
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hρ" => S.compactRepresentation_reducedLieAction
local notation "hτ" => T.compactRepresentation_reducedLieAction
local notation "hι" => S.horizontalCochain_infinitesimal
local notation "hκ" => T.horizontalCochain_infinitesimal

local instance horizontalLinearMapsSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance horizontalLinearMapsTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance horizontalLinearMapsCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Intertwiner

variable {S T}

private theorem horizontalLinearMap_chain (A : S.Intertwiner T) (q : ℕ)
    (f : Langlands.HorizontalAlternating.submodule H σ ρ q) :
    Horizontal.differential H σ τ hσ hτ hκ q (A.horizontalMap q f) =
      A.horizontalMap (q + 1) (Horizontal.differential H σ ρ hσ hρ hι q f) := by
  simpa only [Horizontal.differential, horizontalDifferential,
    horizontalEquivariantSubmodule] using
    (horizontalMap_differential (S := S) (T := T) A q f).symm

/-- The actual cycle intertwiner has the existing restricted chain map underneath. -/
abbrev horizontalCyclesMap_toLinearMap (A : S.Intertwiner T) (q : ℕ) :
    (horizontalCyclesMap (S := S) (T := T) A q).toLinearMap =
      Horizontal.mapCycles H σ ρ τ hσ hρ hτ hι hκ
        (fun q => (A.horizontalMap q).toLinearMap) (horizontalLinearMap_chain A) q := rfl

/-- The actual quotient intertwiner has the existing descended chain map underneath. -/
abbrev horizontalCohomologyMap_toLinearMap (A : S.Intertwiner T) (q : ℕ) :
    (horizontalCohomologyMap (S := S) (T := T) A q).toLinearMap =
      Horizontal.mapCohomology H σ ρ τ hσ hρ hτ hι hκ
        (fun q => (A.horizontalMap q).toLinearMap) (horizontalLinearMap_chain A) q := rfl

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
