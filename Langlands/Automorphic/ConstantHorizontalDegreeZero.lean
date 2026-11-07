import Langlands.Automorphic.HorizontalDegreeZero
import Langlands.Automorphic.ConstantFunctions

/-! # Degree-zero horizontal cohomology of the actual constant automorphic line -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic.ConstantFunctions

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local instance constantHorizontalRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance constantHorizontalContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance constantHorizontalSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance constantHorizontalFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance constantHorizontalStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance constantHorizontalSpaceAddCommGroup :
    AddCommGroup (realization F n).Space := Submodule.addCommGroup _

/-- The full standard compact group fixes every vector of the actual constant line. -/
theorem compactRepresentation_eq_self (k : standardInfiniteCompact F n)
    (f : (realization F n).Space) :
    (realization F n).compactRepresentation k f = f := by
  simpa only [LinearEquiv.apply_symm_apply] using
    compactRepresentation_scalarEquiv F n k ((scalarEquiv F n).symm f)

/-- Every complex Lie direction acts by zero, through the actual enveloping action. -/
theorem complexLieAction_eq_zero (X : ComplexLieAlgebra F n)
    (f : (realization F n).Space) :
    (realization F n).complexLieAction X f = 0 := by
  let c := (scalarEquiv F n).symm f
  have hscalar : augmentation F n (envelopingGenerator F n X) * c = (0 : ℂ) :=
    (congrArg (fun z : ℂ => z * c) (augmentation_envelopingGenerator F n X)).trans
      (zero_mul c)
  have hzero : (realization F n).complexLieAction X (scalarEquiv F n c) = 0 :=
    (envelopingAction_scalarEquiv F n (envelopingGenerator F n X) c).trans
      ((congrArg (fun z : ℂ => scalarEquiv F n z) hscalar).trans
        (scalarEquiv F n).toLinearMap.map_zero)
  exact (congrArg (fun v : (realization F n).Space =>
    (realization F n).complexLieAction X v)
      ((scalarEquiv F n).apply_symm_apply f)).symm.trans hzero

/-- In particular the actual restricted action of every reduced direction vanishes. -/
theorem reducedLieAction_eq_zero (X : ReducedComplexLieAlgebra F n)
    (f : (realization F n).Space) :
    (realization F n).reducedLieAction X f = 0 :=
  complexLieAction_eq_zero F n (reducedComplexInclusion F n X) f

/-- Every actual constant vector is simultaneously compact-fixed and Lie-annihilated. -/
theorem horizontalJointInvariants_eq_top :
    (realization F n).horizontalJointInvariants = ⊤ := by
  apply top_unique
  intro f _
  exact ((realization F n).mem_horizontalJointInvariants f).mpr
    ⟨fun k => compactRepresentation_eq_self F n k f,
      fun X => reducedLieAction_eq_zero F n X f⟩

local instance constantHorizontalInvariantsAddCommGroup :
    AddCommGroup (realization F n).horizontalJointInvariants :=
  Submodule.addCommGroup (R := ℂ) (M := (realization F n).Space) _

/-- Scalars parametrize the simultaneous invariants on their original embedded carrier. -/
def horizontalInvariantScalarEquiv :
    ℂ ≃ₗ[ℂ] (realization F n).horizontalJointInvariants where
  toFun c := ⟨scalarEquiv F n c,
    ((realization F n).mem_horizontalJointInvariants _).mpr
      ⟨fun k => compactRepresentation_scalarEquiv F n k c,
        fun X => reducedLieAction_eq_zero F n X (scalarEquiv F n c)⟩⟩
  invFun f := (scalarEquiv F n).symm f.val
  left_inv c := (scalarEquiv F n).symm_apply_apply c
  right_inv f := Subtype.ext ((scalarEquiv F n).apply_symm_apply f.val)
  map_add' c d := Subtype.ext ((scalarEquiv F n).map_add c d)
  map_smul' z c := Subtype.ext ((scalarEquiv F n).map_smul z c)

@[simp] theorem horizontalInvariantScalarEquiv_val (c : ℂ) :
    (horizontalInvariantScalarEquiv F n c).val = scalarEquiv F n c := rfl

variable [NeZero n]

local instance (q : ℕ) :
    AddCommGroup (horizontalEquivariantSubmodule F n
      (realization F n).compactRepresentation q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := ReducedComplexLieAlgebra F n [⋀^Fin q]→ₗ[ℂ] (realization F n).Space) _
local instance (q : ℕ) : AddCommGroup ((realization F n).horizontalCycles q) :=
  Submodule.addCommGroup (R := ℂ)
    (M := horizontalEquivariantSubmodule F n
      (realization F n).compactRepresentation q) _

/-- The original closed zero cochain with value the actual constant form `c`. -/
def horizontalZeroCycle : ℂ →ₗ[ℂ] (realization F n).horizontalCycles 0 :=
  (realization F n).horizontalCyclesDegreeZeroEquiv.symm.toLinearMap.comp
    (horizontalInvariantScalarEquiv F n).toLinearMap

@[simp] theorem horizontalZeroCycle_apply (c : ℂ)
    (X : Fin 0 → ReducedComplexLieAlgebra F n) :
    (horizontalZeroCycle F n c).val.val X = scalarEquiv F n c := rfl

/-- Evaluation of this zero cochain is the original constant adelic function. -/
@[simp] theorem evaluate_horizontalZeroCycle (c : ℂ)
    (X : Fin 0 → ReducedComplexLieAlgebra F n) (g : AdelicGL F n) :
    evaluate F n ((realization F n).toContinuous
      ((horizontalZeroCycle F n c).val.val X)) g = c :=
  evaluate_scalarEquiv F n c g

set_option maxHeartbeats 100000 in
/-- The class is formed with the existing quotient projection on actual cycles. -/
def horizontalClass : ℂ →ₗ[ℂ] (realization F n).HorizontalCohomology 0 :=
  ((realization F n).horizontalCohomologyClass 0).comp (horizontalZeroCycle F n)

set_option maxHeartbeats 100000 in
/-- Compute the original degree-zero cohomology of the actual constant line. -/
def horizontalScalarEquiv :
    ℂ ≃ₗ[ℂ] (realization F n).HorizontalCohomology 0 :=
  (horizontalInvariantScalarEquiv F n).trans
    (realization F n).horizontalDegreeZeroEquiv.symm

set_option maxHeartbeats 100000 in
@[simp] theorem horizontalScalarEquiv_apply (c : ℂ) :
    horizontalScalarEquiv F n c = horizontalClass F n c := rfl

set_option maxHeartbeats 100000 in
/-- The inverse reads the original cycle's coefficient function at the identity. -/
theorem horizontalScalarEquiv_symm_class (f : (realization F n).horizontalCycles 0) :
    (horizontalScalarEquiv F n).symm
      ((realization F n).horizontalCohomologyClass 0 f) =
        evaluate F n ((realization F n).toContinuous (f.val.val 0)) 1 := by
  change (scalarEquiv F n).symm (f.val.val 0) = _
  exact scalarEquiv_symm_apply F n (f.val.val 0)

set_option maxHeartbeats 100000 in
theorem horizontalCohomology_finrank :
    Module.finrank ℂ ((realization F n).HorizontalCohomology 0) = 1 := by
  rw [← (horizontalScalarEquiv F n).finrank_eq, Module.finrank_self]

set_option maxHeartbeats 100000 in
theorem horizontalClass_eq_zero_iff (c : ℂ) :
    horizontalClass F n c = 0 ↔ c = 0 := by
  change horizontalScalarEquiv F n c = 0 ↔ c = 0
  constructor
  · intro hc
    exact (horizontalScalarEquiv F n).injective
      (hc.trans (map_zero (horizontalScalarEquiv F n)).symm)
  · rintro rfl
    exact map_zero (horizontalScalarEquiv F n)

set_option maxHeartbeats 100000 in
/-- The constant one function gives a nonzero class in the original quotient. -/
theorem horizontalClass_one_ne_zero : horizontalClass F n 1 ≠ 0 := by
  intro h
  exact one_ne_zero ((horizontalClass_eq_zero_iff F n 1).mp h)

end Langlands.Automorphic.ConstantFunctions
