import Langlands.Global.RankinSelberg.RealStandardCompactBanachAction

/-! # Compact-direction control of word derivatives in the compact Banach real standard module -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
-- Resolving the charts on the units of the matrix algebra needs reduction through the
-- normed-ring instances, as in `RealStandardCompactSmoothVectors`.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

/-- In the compact Banach realization `representation ds` of the real standard module of
`GL_{r+1}(ℝ)` attached to a block list `ds` of rank `r + 1`, every word derivative of a smooth
vector is controlled in the Banach norm by word derivatives along skew-symmetric matrices: for
each word `Xs` of real matrices there are a finite set `T` of words whose letters `Y` all satisfy
`Yᵀ = -Y` and a constant `C ≥ 0` with
`‖dπ(Xs) v‖ ≤ C ∑_{w ∈ T} ‖dπ(w) v‖` for every smooth vector `v`. The set `T` and the constant
`C` depend on `r`, `ds` and `Xs` only; `T` may contain the empty word. -/
def RealStandardCompactWordControlStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
      ∃ (T : Finset (List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ))) (C : ℝ),
        0 ≤ C ∧ (∀ w ∈ T, ∀ Y ∈ w, Yᵀ = -Y) ∧
        ∀ v : smoothVectors (matrixModel ℝ (r + 1)) (representation (n := r + 1) ds),
          ‖iteratedLieDerivative (matrixModel ℝ (r + 1)) (representation (n := r + 1) ds)
              Xs v‖ ≤
            C * ∑ w ∈ T, ‖iteratedLieDerivative (matrixModel ℝ (r + 1))
              (representation (n := r + 1) ds) w v‖

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
