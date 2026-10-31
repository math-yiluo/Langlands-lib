import Langlands.Automorphic.HorizontalCohomologyTransport
import Langlands.Automorphic.HorizontalCohomologyClasses

/-! # Identity and composition for actual horizontal quotient transport -/

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

local instance horizontalQuotientFunctorLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T U : OperatorRealization F n)

local instance horizontalQuotientFunctorLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsThirdGroup : AddCommGroup U.Space :=
  Submodule.addCommGroup _

local instance horizontalQuotientFunctorLawsSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      S.compactRepresentation q) :=
  Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      T.compactRepresentation q) :=
  Submodule.addCommGroup _
local instance horizontalQuotientFunctorLawsThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      U.compactRepresentation q) :=
  Submodule.addCommGroup _
local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)

local instance horizontalQuotientFunctorLawsCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Intertwiner

variable {S T U}

/-- The identity full operator map acts identically on every actual quotient class. -/
abbrev horizontalCohomologyMap_id_apply (q : ℕ) (z : S.HorizontalCohomology q) :
    horizontalCohomologyMap (S := S) (T := S)
        (Representation.IntertwiningMap.id S.representation) q z = z := by
  refine Quotient.inductionOn' z ?_
  intro f
  change S.horizontalCohomologyClass q
      (horizontalCyclesMap (S := S) (T := S)
        (Representation.IntertwiningMap.id S.representation) q f) =
    S.horizontalCohomologyClass q f
  apply congrArg (S.horizontalCohomologyClass q)
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Identity transport as equality of bundled finite adelic quotient intertwiners. -/
abbrev horizontalCohomologyMap_id (q : ℕ) :
    horizontalCohomologyMap (S := S) (T := S)
        (Representation.IntertwiningMap.id S.representation) q =
      Representation.IntertwiningMap.id (S.horizontalCohomologyFiniteRepresentation q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (horizontalCohomologyMap_id_apply (S := S) q)

/-- Transport by a full composite agrees with successive quotient transport. -/
abbrev horizontalCohomologyMap_comp_apply (A : S.Intertwiner T) (B : T.Intertwiner U)
    (q : ℕ) (z : S.HorizontalCohomology q) :
    horizontalCohomologyMap (S := S) (T := U) (B.comp A) q z =
      horizontalCohomologyMap (S := T) (T := U) B q
        (horizontalCohomologyMap (S := S) (T := T) A q z) := by
  refine Quotient.inductionOn' z ?_
  intro f
  change U.horizontalCohomologyClass q
      (horizontalCyclesMap (S := S) (T := U) (B.comp A) q f) =
    U.horizontalCohomologyClass q
      (horizontalCyclesMap (S := T) (T := U) B q
        (horizontalCyclesMap (S := S) (T := T) A q f))
  apply congrArg (U.horizontalCohomologyClass q)
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Composition transport as equality of bundled finite adelic quotient intertwiners. -/
abbrev horizontalCohomologyMap_comp (A : S.Intertwiner T) (B : T.Intertwiner U)
    (q : ℕ) :
    horizontalCohomologyMap (S := S) (T := U) (B.comp A) q =
      (horizontalCohomologyMap (S := T) (T := U) B q).comp
        (horizontalCohomologyMap (S := S) (T := T) A q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (horizontalCohomologyMap_comp_apply A B q)

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
