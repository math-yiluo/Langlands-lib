import Langlands.Automorphic.HorizontalCohomology
import Langlands.Automorphic.HorizontalDifferentialFinite
import Langlands.Cohomology.Lie.HorizontalCohomologyAction

/-! # Actual finite adelic action on horizontal cohomology -/

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

local instance horizontalCohomologyFiniteRationalGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyFiniteContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalCohomologyFiniteFormsGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalCohomologyFiniteStableGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance horizontalCohomologyFiniteSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _
local instance horizontalCohomologyFiniteCochainGroup (q : ℕ) :
    AddCommGroup (horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Submodule.addCommGroup _

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "ρ" => S.compactRepresentation
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hρ" => S.compactRepresentation_reducedLieAction
local notation "hι" => S.horizontalCochain_infinitesimal

/-- Actual finite translation restricted to the closed horizontal cochains. -/
abbrev horizontalCyclesFiniteRepresentation (q : ℕ) :=
  Horizontal.cyclesRepresentation H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q

/-- The cycle action has the same underlying finite-translated cochain. -/
abbrev horizontalCyclesFiniteRepresentation_val (q : ℕ) (d : FiniteAdelicGL F n)
    (f : S.horizontalCycles q) :=
  Horizontal.cyclesRepresentation_val H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q d f

/-- Actual finite adelic translation on the existing horizontal quotient. -/
abbrev horizontalCohomologyFiniteRepresentation (q : ℕ) :=
  Horizontal.cohomologyRepresentation H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q

/-- A translated class is represented by the translated actual cycle. -/
abbrev horizontalCohomologyFiniteRepresentation_class (q : ℕ) (d : FiniteAdelicGL F n)
    (f : S.horizontalCycles q) :=
  Horizontal.cohomologyRepresentation_class H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q d f

/-- The actual quotient projection intertwines finite adelic translation. -/
abbrev horizontalCohomologyClassFiniteIntertwiner (q : ℕ) :=
  Horizontal.cohomologyClassIntertwiner H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q

/-- The finite intertwiner is the existing actual cohomology projection. -/
abbrev horizontalCohomologyClassFiniteIntertwiner_toLinearMap (q : ℕ) :=
  Horizontal.cohomologyClassIntertwiner_toLinearMap H σ ρ hσ hρ hι
    S.horizontalFiniteRepresentation S.horizontalDifferential_finite q

end OperatorRealization
end Langlands.Automorphic
