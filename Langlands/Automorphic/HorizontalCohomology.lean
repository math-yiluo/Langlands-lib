import Langlands.Automorphic.HorizontalDifferential
import Langlands.Cohomology.Lie.HorizontalCohomology

/-! # Actual horizontal cohomology of an automorphic realization -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance (q : ℕ) :
    AddCommGroup (horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Submodule.addCommGroup _

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "ρ" => S.compactRepresentation
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hρ" => S.compactRepresentation_reducedLieAction
local notation "hι" => S.horizontalCochain_infinitesimal

/-- Closed cochains for the actual automorphic horizontal differential. -/
abbrev horizontalCycles (q : ℕ) := Horizontal.cycles H σ ρ hσ hρ hι q

/-- Zero boundaries in degree zero and actual differential images in successors. -/
abbrev horizontalBoundaries (q : ℕ) := Horizontal.boundaries H σ ρ hσ hρ hι q

/-- The actual boundary inclusion range inside closed horizontal cochains. -/
abbrev horizontalBoundariesInCycles (q : ℕ) :=
  Horizontal.boundariesInCycles H σ ρ hσ hρ hι q

/-- Cohomology of the actual horizontal full-compact-equivariant differential. -/
abbrev HorizontalCohomology (q : ℕ) :=
  Horizontal.HorizontalCohomology H σ ρ hσ hρ hι q

/-- The quotient projection from actual horizontal cycles. -/
abbrev horizontalCohomologyClass (q : ℕ) :=
  Horizontal.cohomologyClass H σ ρ hσ hρ hι q

end OperatorRealization
end Langlands.Automorphic
