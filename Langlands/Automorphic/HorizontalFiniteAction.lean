import Langlands.Automorphic.HorizontalDifferential

/-! # Finite adelic action on actual horizontal cochains -/

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
local instance horizontalFiniteActionRationalInvariantAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance horizontalFiniteActionContinuousRationalAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalFiniteActionFiniteSmoothRationalAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance horizontalFiniteActionAutomorphicFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance horizontalFiniteActionStableAutomorphicAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance horizontalFiniteActionSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _

/-- Actual finite translation, viewed as a full-compact coefficient intertwiner. -/
def finiteCompactIntertwiner (d : FiniteAdelicGL F n) :
    S.compactRepresentation.IntertwiningMap S.compactRepresentation where
  toLinearMap := S.finiteRepresentation d
  isIntertwining' k := LinearMap.ext (S.finiteRepresentation_compactRepresentation d k)

/-- The same finite translation is a map of the actual reduced Lie module. -/
def finiteReducedLieHom (d : FiniteAdelicGL F n) :
    S.Space →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ S.Space where
  toLinearMap := S.finiteRepresentation d
  map_lie' := S.finiteRepresentation_reducedLieAction d _ _

/-- Finite adelic translation on the existing horizontal full-compact spaces. -/
def horizontalFiniteRepresentation (q : ℕ) :
    Representation ℂ (FiniteAdelicGL F n)
      (horizontalEquivariantSubmodule F n S.compactRepresentation q) where
  toFun d := horizontalMapCoefficients F n q (S.finiteCompactIntertwiner d)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    change S.finiteRepresentation 1 (f.val X) = f.val X
    simp only [map_one, Module.End.one_apply]
  map_mul' d e := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    change S.finiteRepresentation (d * e) (f.val X) =
      S.finiteRepresentation d (S.finiteRepresentation e (f.val X))
    simp only [map_mul, Module.End.mul_apply]

@[simp]
theorem horizontalFiniteRepresentation_apply (q : ℕ) (d : FiniteAdelicGL F n)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (S.horizontalFiniteRepresentation q d f).val X =
      S.finiteRepresentation d (f.val X) := rfl

end OperatorRealization
end Langlands.Automorphic
