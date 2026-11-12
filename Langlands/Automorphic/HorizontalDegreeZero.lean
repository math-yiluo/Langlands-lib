import Langlands.Automorphic.HorizontalCohomology
import Langlands.Cohomology.Lie.HorizontalDegreeZero

/-! # Degree zero of actual automorphic horizontal cohomology -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL
open Langlands.Cohomology.Lie

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance horizontalZeroRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalZeroContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalZeroSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalZeroFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalZeroStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance horizontalZeroSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalZeroEquivariantAddCommGroup (q : ℕ) :
    AddCommGroup (horizontalEquivariantSubmodule F n S.compactRepresentation q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ] S.Space) _
local instance (q : ℕ) : AddCommGroup (S.horizontalCycles q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := horizontalEquivariantSubmodule F n S.compactRepresentation q) _

local notation "H" => compactInReducedSubmodule F n
local notation "σ" => reducedCompactRepresentation F n
local notation "ρ" => S.compactRepresentation
local notation "hσ" =>
  (fun k X Y => LieEquiv.map_lie (reducedComplexLieConjugation F n (Subtype.val k)) X Y)
local notation "hρ" => S.compactRepresentation_reducedLieAction
local notation "hι" => S.horizontalCochain_infinitesimal

/-- Actual vectors fixed by the full compact group and killed by the reduced Lie algebra. -/
def horizontalJointInvariants : Submodule ℂ S.Space :=
  Horizontal.jointInvariants (L := ReducedComplexLieAlgebra F n) ρ

omit [NeZero n] in
@[simp] theorem mem_horizontalJointInvariants (f : S.Space) :
    f ∈ S.horizontalJointInvariants ↔
      (∀ k, S.compactRepresentation k f = f) ∧
      (∀ X, S.reducedLieAction X f = 0) := Iff.rfl

/-- Closed zero cochains for the actual differential are simultaneous invariants. -/
def horizontalCyclesDegreeZeroEquiv :
    S.horizontalCycles 0 ≃ₗ[ℂ] S.horizontalJointInvariants :=
  Horizontal.cyclesDegreeZeroEquiv H σ ρ hσ hρ hι

@[simp] theorem horizontalCyclesDegreeZeroEquiv_apply (f : S.horizontalCycles 0) :
    (S.horizontalCyclesDegreeZeroEquiv f).val = f.val.val 0 := rfl

@[simp] theorem horizontalCyclesDegreeZeroEquiv_symm_apply
    (f : S.horizontalJointInvariants) (X : Fin 0 → ReducedComplexLieAlgebra F n) :
    (S.horizontalCyclesDegreeZeroEquiv.symm f).val.val X = f.val := rfl

/-- The original boundary inclusion range vanishes in degree zero. -/
@[simp] theorem horizontalBoundariesInCycles_zero :
    S.horizontalBoundariesInCycles 0 = ⊥ :=
  Horizontal.boundariesInCycles_zero H σ ρ hσ hρ hι

set_option maxHeartbeats 100000 in
/-- Compute the existing automorphic degree-zero quotient, with all premises discharged. -/
def horizontalDegreeZeroEquiv :
    S.HorizontalCohomology 0 ≃ₗ[ℂ] S.horizontalJointInvariants :=
  Horizontal.degreeZeroEquiv H σ ρ hσ hρ hι

/-- The original class of a zero cycle maps to its coefficient value. -/
@[simp] theorem horizontalDegreeZeroEquiv_class (f : S.horizontalCycles 0) :
    (S.horizontalDegreeZeroEquiv (S.horizontalCohomologyClass 0 f)).val =
      f.val.val 0 := rfl

set_option maxHeartbeats 100000 in
/-- A simultaneous invariant gives the original class of the constant zero cochain. -/
@[simp] theorem horizontalDegreeZeroEquiv_symm (f : S.horizontalJointInvariants) :
    S.horizontalDegreeZeroEquiv.symm f =
      S.horizontalCohomologyClass 0 (S.horizontalCyclesDegreeZeroEquiv.symm f) := rfl

set_option maxHeartbeats 100000 in
theorem horizontalDegreeZeroEquiv_symm_ne_zero (f : S.horizontalJointInvariants)
    (hf : f.val ≠ 0) :
    S.horizontalDegreeZeroEquiv.symm f ≠ 0 :=
  Horizontal.degreeZeroEquiv_symm_ne_zero H σ ρ hσ hρ hι f hf

end OperatorRealization
end Langlands.Automorphic
