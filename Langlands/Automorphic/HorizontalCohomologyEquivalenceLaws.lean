import Langlands.Automorphic.HorizontalCohomologyEquivalence
import Langlands.Automorphic.HorizontalCohomologyTransport
import Langlands.Automorphic.HorizontalCohomologyClasses

/-! # Underlying transport and class formulas for actual horizontal equivalences -/

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

local instance horizontalCohomologyEquivalenceLawsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalCohomologyEquivalenceLawsSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsTargetGroup : AddCommGroup T.Space :=
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

local instance horizontalCohomologyEquivalenceLawsSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceLawsCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Equivalence

variable {S T}

/-- The cycle equivalence has the existing actual forward cycle intertwiner. -/
abbrev horizontalCyclesEquiv_toIntertwiningMap (e : S.Equivalence T) (q : ℕ) :
    (e.horizontalCyclesEquiv q).toIntertwiningMap =
      Intertwiner.horizontalCyclesMap (S := S) (T := T) e.toIntertwiningMap q := rfl

/-- The quotient equivalence has the existing actual forward quotient intertwiner. -/
abbrev horizontalCohomologyEquiv_toIntertwiningMap (e : S.Equivalence T) (q : ℕ) :
    (e.horizontalCohomologyEquiv q).toIntertwiningMap =
      Intertwiner.horizontalCohomologyMap (S := S) (T := T) e.toIntertwiningMap q := rfl

/-- The underlying cochain is transported by the actual horizontal cochain equivalence. -/
abbrev horizontalCyclesEquiv_val (e : S.Equivalence T) (q : ℕ)
    (f : S.horizontalCycles q) :
    (e.horizontalCyclesEquiv q f).val = e.horizontalEquiv q f.val := rfl

/-- Evaluation of a transported cycle is full operator coefficient postcomposition. -/
abbrev horizontalCyclesEquiv_apply (e : S.Equivalence T) (q : ℕ)
    (f : S.horizontalCycles q) (X : Fin q → ReducedComplexLieAlgebra F n) :
    (e.horizontalCyclesEquiv q f).val.val X = e (f.val.val X) := rfl

/-- Forward quotient transport sends each cycle class to its transported class. -/
abbrev horizontalCohomologyEquiv_class (e : S.Equivalence T) (q : ℕ)
    (f : S.horizontalCycles q) :
    e.horizontalCohomologyEquiv q (S.horizontalCohomologyClass q f) =
      T.horizontalCohomologyClass q (e.horizontalCyclesEquiv q f) := rfl

/-- The inverse quotient equivalence has the corresponding cycle representative formula. -/
abbrev horizontalCohomologyEquiv_symm_class (e : S.Equivalence T) (q : ℕ)
    (f : T.horizontalCycles q) :
    (e.horizontalCohomologyEquiv q).symm (T.horizontalCohomologyClass q f) =
      S.horizontalCohomologyClass q ((e.horizontalCyclesEquiv q).symm f) := rfl

end Equivalence
end OperatorRealization
end Langlands.Automorphic
