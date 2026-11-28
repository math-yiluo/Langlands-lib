import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction

/-! # Closed reverse intertwiners for real standard modules -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation:max "V" n:max ds:max =>
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
local notation:max "D" rank:max ds:max =>
  DerivativeSmoothVectors (matrixModel ℝ rank) (representation (n := rank) ds)

/-- A Langlands-ordered real standard module admits a nonzero reverse
intertwiner with a continuous extension of closed range. -/
def RealStandardClosedReverseStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → IsRealLanglandsOrdered ds →
    ∃ (A : V (r + 1) ds →ₗ[ℂ] V (r + 1) ds.reverse)
      (T : D (r + 1) ds →L[ℂ] D (r + 1) ds.reverse),
      A ≠ 0 ∧ IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) ds.reverse)
        (realStandardLie (r + 1) ds.reverse) ds A ∧
      IsClosed (Set.range T) ∧ ∀ v,
        T (compactFiniteEquiv (n := r + 1) ds v).val =
          (compactFiniteEquiv (n := r + 1) ds.reverse (A v)).val

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
