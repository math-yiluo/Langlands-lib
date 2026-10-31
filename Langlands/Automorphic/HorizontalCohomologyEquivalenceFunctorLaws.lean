import Langlands.Automorphic.HorizontalCohomologyEquivalence
import Langlands.Automorphic.HorizontalCohomologyClasses

/-! # Inversion and functor laws for actual horizontal equivalences -/

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

local instance horizontalEquivalenceFunctorLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T U : OperatorRealization F n)

local instance horizontalEquivalenceFunctorLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsTargetGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsThirdGroup : AddCommGroup U.Space :=
  Submodule.addCommGroup _

local instance horizontalEquivalenceFunctorLawsSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      S.compactRepresentation q) :=
  Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      T.compactRepresentation q) :=
  Submodule.addCommGroup _
local instance horizontalEquivalenceFunctorLawsThirdCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule
      (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
      U.compactRepresentation q) :=
  Submodule.addCommGroup _
local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)

local instance horizontalEquivalenceFunctorLawsCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Equivalence

variable {S T U}

/-- Inverting a full operator equivalence inverts its actual cycle equivalence. -/
abbrev horizontalCyclesEquiv_symm (e : S.Equivalence T) (q : ℕ) :
    (e.horizontalCyclesEquiv q).symm =
      horizontalCyclesEquiv (S := T) (T := S) e.symm q := by
  apply Representation.Equiv.ext
  funext f
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Inverting a full operator equivalence inverts its actual quotient equivalence. -/
abbrev horizontalCohomologyEquiv_symm (e : S.Equivalence T) (q : ℕ) :
    (e.horizontalCohomologyEquiv q).symm =
      horizontalCohomologyEquiv (S := T) (T := S) e.symm q := by
  apply Representation.Equiv.ext
  funext z
  refine Quotient.inductionOn' z ?_
  intro f
  change S.horizontalCohomologyClass q ((e.horizontalCyclesEquiv q).symm f) =
    S.horizontalCohomologyClass q
      (horizontalCyclesEquiv (S := T) (T := S) e.symm q f)
  apply congrArg (S.horizontalCohomologyClass q)
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- The identity full operator equivalence acts identically on actual cycles. -/
abbrev horizontalCyclesEquiv_refl (q : ℕ) :
    horizontalCyclesEquiv (S := S) (T := S)
        (Representation.Equiv.refl S.representation) q =
      Representation.Equiv.refl (S.horizontalCyclesFiniteRepresentation q) := by
  apply Representation.Equiv.ext
  funext f
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- The identity full operator equivalence acts identically on actual cohomology. -/
abbrev horizontalCohomologyEquiv_refl (q : ℕ) :
    horizontalCohomologyEquiv (S := S) (T := S)
        (Representation.Equiv.refl S.representation) q =
      Representation.Equiv.refl (S.horizontalCohomologyFiniteRepresentation q) := by
  apply Representation.Equiv.ext
  funext z
  refine Quotient.inductionOn' z ?_
  intro f
  change S.horizontalCohomologyClass q
      (horizontalCyclesEquiv (S := S) (T := S)
        (Representation.Equiv.refl S.representation) q f) =
    S.horizontalCohomologyClass q f
  apply congrArg (S.horizontalCohomologyClass q)
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Cycle equivalences preserve composition with the first equivalence applied first. -/
abbrev horizontalCyclesEquiv_trans (e : S.Equivalence T) (g : T.Equivalence U)
    (q : ℕ) :
    horizontalCyclesEquiv (S := S) (T := U) (e.trans g) q =
      (e.horizontalCyclesEquiv q).trans (g.horizontalCyclesEquiv q) := by
  apply Representation.Equiv.ext
  funext f
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- The quotient equivalences preserve composition in the same order. -/
abbrev horizontalCohomologyEquiv_trans (e : S.Equivalence T) (g : T.Equivalence U)
    (q : ℕ) :
    horizontalCohomologyEquiv (S := S) (T := U) (e.trans g) q =
      (e.horizontalCohomologyEquiv q).trans (g.horizontalCohomologyEquiv q) := by
  apply Representation.Equiv.ext
  funext z
  refine Quotient.inductionOn' z ?_
  intro f
  change U.horizontalCohomologyClass q
      (horizontalCyclesEquiv (S := S) (T := U) (e.trans g) q f) =
    U.horizontalCohomologyClass q
      (g.horizontalCyclesEquiv q (e.horizontalCyclesEquiv q f))
  apply congrArg (U.horizontalCohomologyClass q)
  apply Subtype.ext
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

end Equivalence
end OperatorRealization
end Langlands.Automorphic
