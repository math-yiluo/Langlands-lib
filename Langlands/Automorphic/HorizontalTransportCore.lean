import Langlands.Automorphic.HorizontalDifferentialFinite

/-! # Transport of actual horizontal cochains by full operator intertwiners -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T U : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _
local instance : AddCommGroup U.Space := Submodule.addCommGroup _


namespace Intertwiner

variable {S T U}

/-- A full operator intertwiner transports the actual horizontal finite action. -/
def horizontalMap (A : S.Intertwiner T) (q : ℕ) :
    (S.horizontalFiniteRepresentation q).IntertwiningMap
      (T.horizontalFiniteRepresentation q) where
  toLinearMap := horizontalMapCoefficients F n q A.compactRestriction
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact A.finite d (f.val X)

@[simp]
theorem horizontalMap_apply (A : S.Intertwiner T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (A.horizontalMap q f).val X = A (f.val X) := rfl

@[simp]
theorem horizontalMap_id (q : ℕ) :
    horizontalMap (S := S) (T := S)
        (Representation.IntertwiningMap.id S.representation) q =
      Representation.IntertwiningMap.id (S.horizontalFiniteRepresentation q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

@[simp]
theorem horizontalMap_comp (A : S.Intertwiner T) (B : T.Intertwiner U) (q : ℕ) :
    horizontalMap (S := S) (T := U) (B.comp A) q =
      (B.horizontalMap q).comp (A.horizontalMap q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Transport by a full intertwiner commutes with the actual differential. -/
theorem horizontalMap_differential [NeZero n] (A : S.Intertwiner T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    A.horizontalMap (q + 1) (S.horizontalDifferential q f) =
      T.horizontalDifferential q (A.horizontalMap q f) := by
  apply Subtype.ext
  exact Langlands.Cohomology.Lie.map_differential A.reducedLieRestriction q f.val

/-- The naturality square is an equality of finite adelic intertwiners. -/
theorem horizontalMap_differential_comp [NeZero n]
    (A : S.Intertwiner T) (q : ℕ) :
    (A.horizontalMap (q + 1)).comp (S.horizontalDifferentialIntertwiner q) =
      (T.horizontalDifferentialIntertwiner q).comp (A.horizontalMap q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (A.horizontalMap_differential q)

end Intertwiner
end OperatorRealization
end Langlands.Automorphic
