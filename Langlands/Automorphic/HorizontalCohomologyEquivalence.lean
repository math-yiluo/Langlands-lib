import Langlands.Automorphic.HorizontalEquivalence
import Langlands.Automorphic.HorizontalCohomologyFinite
import Langlands.Cohomology.Lie.HorizontalCohomologyEquivalence

/-! # Full operator equivalences on actual horizontal cohomology representations -/

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

local instance horizontalCohomologyEquivalenceRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalCohomologyEquivalenceSourceGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceTargetGroup : AddCommGroup T.Space :=
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

local instance horizontalCohomologyEquivalenceSourceCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ ρ q) :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceTargetCochainGroup (q : ℕ) :
    AddCommGroup (Langlands.HorizontalAlternating.submodule H σ τ q) :=
  Submodule.addCommGroup _
local instance horizontalCohomologyEquivalenceCycleGroup
    (R : OperatorRealization F n) (q : ℕ) :
    AddCommGroup (Horizontal.cycles H σ R.compactRepresentation hσ
      R.compactRepresentation_reducedLieAction R.horizontalCochain_infinitesimal q) :=
  Submodule.addCommGroup _

namespace Equivalence

variable {S T}

private theorem horizontalEquiv_chain (e : S.Equivalence T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    Horizontal.differential H σ τ hσ hτ hκ q (e.horizontalEquiv q f) =
      e.horizontalEquiv (q + 1) (Horizontal.differential H σ ρ hσ hρ hι q f) := by
  simpa only [Horizontal.differential, horizontalDifferential,
    horizontalEquivariantSubmodule] using
    (horizontalEquiv_differential (S := S) (T := T) e q f).symm

/-- Restrict the actual full operator equivalence to horizontal cycles. -/
def horizontalCyclesEquiv (e : S.Equivalence T) (q : ℕ) :
    (S.horizontalCyclesFiniteRepresentation q).Equiv
      (T.horizontalCyclesFiniteRepresentation q) :=
  Horizontal.equivCycles H σ ρ τ hσ hρ hτ hι hκ
    S.horizontalFiniteRepresentation T.horizontalFiniteRepresentation
    S.horizontalDifferential_finite T.horizontalDifferential_finite
    e.horizontalEquiv (horizontalEquiv_chain e) q

/-- Descend the actual full operator equivalence to horizontal cohomology. -/
def horizontalCohomologyEquiv (e : S.Equivalence T) (q : ℕ) :
    (S.horizontalCohomologyFiniteRepresentation q).Equiv
      (T.horizontalCohomologyFiniteRepresentation q) :=
  Horizontal.equivCohomology H σ ρ τ hσ hρ hτ hι hκ
    S.horizontalFiniteRepresentation T.horizontalFiniteRepresentation
    S.horizontalDifferential_finite T.horizontalDifferential_finite
    e.horizontalEquiv (horizontalEquiv_chain e) q

end Equivalence
end OperatorRealization
end Langlands.Automorphic
