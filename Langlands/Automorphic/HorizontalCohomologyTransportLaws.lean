import Langlands.Automorphic.HorizontalCohomologyTransport
import Langlands.Automorphic.HorizontalCohomologyClasses

/-! # Formulas and laws for actual horizontal quotient transport -/

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

local instance horizontalQuotientTransportLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalQuotientTransportLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _

local instance horizontalQuotientTransportLawsSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      S.compactRepresentation q) :=
  Submodule.addCommGroup _
local instance horizontalQuotientTransportLawsTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      T.compactRepresentation q) :=
  Submodule.addCommGroup _
local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)

local instance horizontalQuotientTransportLawsCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Intertwiner

variable {S T}

/-- A class is sent to the class of its transported actual cycle. -/
abbrev horizontalCohomologyMap_class (A : S.Intertwiner T) (q : ℕ)
    (f : S.horizontalCycles q) :
    horizontalCohomologyMap (S := S) (T := T) A q (S.horizontalCohomologyClass q f) =
      T.horizontalCohomologyClass q (horizontalCyclesMap (S := S) (T := T) A q f) := rfl

/-- Naturality of the actual finite-equivariant quotient projection. -/
abbrev horizontalCohomologyMap_class_comp (A : S.Intertwiner T) (q : ℕ) :
    (horizontalCohomologyMap (S := S) (T := T) A q).comp
        (S.horizontalCohomologyClassFiniteIntertwiner q) =
      (T.horizontalCohomologyClassFiniteIntertwiner q).comp
        (horizontalCyclesMap (S := S) (T := T) A q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (fun _ => rfl)

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
