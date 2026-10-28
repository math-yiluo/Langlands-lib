import Langlands.Automorphic.HorizontalCohomology

/-! # Classes in actual automorphic horizontal cohomology -/

noncomputable section

universe u uK uL uM uG

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

/-- Boundary inclusion for the actual automorphic differential. -/
abbrev horizontalBoundaries_le_cycles (q : ℕ) :=
  Horizontal.boundaries_le_cycles H σ ρ hσ hρ hι q

/-- Boundary membership inside the actual cycle module. -/
abbrev mem_horizontalBoundariesInCycles {q : ℕ} {f : S.horizontalCycles q} :=
  Horizontal.mem_boundariesInCycles H σ ρ hσ hρ hι (f := f)

/-- Every actual cohomology class has a closed horizontal representative. -/
abbrev horizontalCohomologyClass_surjective (q : ℕ) :=
  Horizontal.cohomologyClass_surjective H σ ρ hσ hρ hι q

/-- A closed horizontal cochain has zero class precisely when it is a boundary. -/
abbrev horizontalCohomologyClass_eq_zero {q : ℕ} (f : S.horizontalCycles q) :=
  Horizontal.cohomologyClass_eq_zero H σ ρ hσ hρ hι f

/-- Equal classes differ by an actual horizontal coboundary. -/
abbrev horizontalCohomologyClass_eq_iff {q : ℕ} (f g : S.horizontalCycles q) :=
  Horizontal.cohomologyClass_eq_iff H σ ρ hσ hρ hι f g

/-- The actual horizontal differential with its codomain restricted to cycles. -/
abbrev horizontalCoboundaryToCycles (q : ℕ) :=
  Horizontal.coboundaryToCycles H σ ρ hσ hρ hι q

/-- Every actual horizontal coboundary has zero cohomology class. -/
abbrev horizontalCohomologyClass_coboundary (q : ℕ)
    (f : horizontalEquivariantSubmodule F n ρ q) :=
  Horizontal.cohomologyClass_coboundary H σ ρ hσ hρ hι q f

end OperatorRealization
end Langlands.Automorphic
