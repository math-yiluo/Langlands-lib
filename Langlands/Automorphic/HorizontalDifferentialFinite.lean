import Langlands.Automorphic.HorizontalFiniteAction

/-! # Finite equivariance of the actual horizontal differential -/

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

variable (S : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

section Differential

variable [NeZero n]

/-- The actual horizontal differential commutes with every finite translation. -/
theorem horizontalDifferential_finite (q : ℕ) (d : FiniteAdelicGL F n)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    S.horizontalDifferential q (S.horizontalFiniteRepresentation q d f) =
      S.horizontalFiniteRepresentation (q + 1) d (S.horizontalDifferential q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (S.finiteReducedLieHom d) q f.val).symm

/-- The horizontal differential is a genuine finite adelic intertwiner. -/
def horizontalDifferentialIntertwiner (q : ℕ) :
    (S.horizontalFiniteRepresentation q).IntertwiningMap
      (S.horizontalFiniteRepresentation (q + 1)) where
  toLinearMap := S.horizontalDifferential q
  isIntertwining' d := LinearMap.ext (S.horizontalDifferential_finite q d)

@[simp]
theorem horizontalDifferentialIntertwiner_toLinearMap (q : ℕ) :
    (S.horizontalDifferentialIntertwiner q).toLinearMap =
      S.horizontalDifferential q := rfl

end Differential

end OperatorRealization
end Langlands.Automorphic
