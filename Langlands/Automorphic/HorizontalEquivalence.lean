import Langlands.Automorphic.HorizontalTransportCore

/-! # Equivalence transport of actual horizontal cochains and differentials -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

-- Explicit names keep these canonical local structures from colliding with
-- generated instance names in sibling modules imported alongside this one.
local instance horizontalEquivalenceRationalInvariantAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceContinuousRationalAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceFiniteSmoothRationalAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceAutomorphicFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalEquivalenceStableAutomorphicAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance horizontalEquivalenceSSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance horizontalEquivalenceTSpaceAddCommGroup : AddCommGroup T.Space :=
  Submodule.addCommGroup _


namespace Equivalence

variable {S T}

/-- Full operator equivalences transport horizontal spaces and their finite actions. -/
def horizontalEquiv (e : S.Equivalence T) (q : ℕ) :
    (S.horizontalFiniteRepresentation q).Equiv (T.horizontalFiniteRepresentation q) :=
  Representation.Equiv.mk
    (horizontalCoefficientEquiv F n q e.compactRestriction)
    (Intertwiner.horizontalMap (S := S) (T := T) e.toIntertwiningMap q).isIntertwining'

@[simp]
theorem horizontalEquiv_apply (e : S.Equivalence T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (e.horizontalEquiv q f).val X = e (f.val X) := rfl

@[simp]
theorem horizontalEquiv_toLinearMap (e : S.Equivalence T) (q : ℕ) :
    (e.horizontalEquiv q).toLinearEquiv.toLinearMap =
      (Intertwiner.horizontalMap (S := S) (T := T) e.toIntertwiningMap q).toLinearMap := rfl

/-- The equivalence transports the same differential in every degree. -/
theorem horizontalEquiv_differential [NeZero n] (e : S.Equivalence T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    e.horizontalEquiv (q + 1) (S.horizontalDifferential q f) =
      T.horizontalDifferential q (e.horizontalEquiv q f) :=
  Intertwiner.horizontalMap_differential (S := S) (T := T) e.toIntertwiningMap q f

end Equivalence

end OperatorRealization
end Langlands.Automorphic
