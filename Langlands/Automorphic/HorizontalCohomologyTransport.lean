import Langlands.Automorphic.HorizontalTransportCore
import Langlands.Automorphic.HorizontalCohomologyFinite
import Langlands.Cohomology.Lie.HorizontalCohomologyIntertwiner

/-! # Full operator maps on actual horizontal cohomology representations -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance horizontalCohomologyTransportRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyTransportContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyTransportSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyTransportFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCohomologyTransportStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalCohomologyTransportSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalCohomologyTransportTargetGroup : AddCommGroup T.Space :=
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

namespace Intertwiner

variable {S T}

private theorem horizontalMap_chain (A : S.Intertwiner T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    Horizontal.differential H σ τ hσ hτ hκ q (A.horizontalMap q f) =
      A.horizontalMap (q + 1) (Horizontal.differential H σ ρ hσ hρ hι q f) := by
  simpa only [Horizontal.differential, horizontalDifferential,
    horizontalEquivariantSubmodule] using
    (horizontalMap_differential (S := S) (T := T) A q f).symm

/-- Restrict the actual full operator map to the existing horizontal cycles. -/
def horizontalCyclesMap (A : S.Intertwiner T) (q : ℕ) :
    (S.horizontalCyclesFiniteRepresentation q).IntertwiningMap
      (T.horizontalCyclesFiniteRepresentation q) :=
  Horizontal.mapCyclesIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    S.horizontalFiniteRepresentation T.horizontalFiniteRepresentation
    S.horizontalDifferential_finite T.horizontalDifferential_finite
    A.horizontalMap (horizontalMap_chain A) q

/-- Descend the actual full operator map to the existing cohomology quotient. -/
def horizontalCohomologyMap (A : S.Intertwiner T) (q : ℕ) :
    (S.horizontalCohomologyFiniteRepresentation q).IntertwiningMap
      (T.horizontalCohomologyFiniteRepresentation q) :=
  Horizontal.mapCohomologyIntertwiner H σ ρ τ hσ hρ hτ hι hκ
    S.horizontalFiniteRepresentation T.horizontalFiniteRepresentation
    S.horizontalDifferential_finite T.horizontalDifferential_finite
    A.horizontalMap (horizontalMap_chain A) q

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
