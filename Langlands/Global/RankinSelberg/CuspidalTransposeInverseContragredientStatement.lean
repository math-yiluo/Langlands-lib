import Langlands.Automorphic.Contragredient
import Langlands.Global.RankinSelberg.UnequalIntegrals

/-! # The dual cusp forms realize the contragredient

For an actual cuspidal operator realization `T` of `GL_(r+1)`, the dual cusp forms
`φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp forms `φ` of `T` lie in an actual cuspidal operator
realization of the contragredient of `T` (Cogdell 2004, pp.201, 203 and 206: Gelfand and
Kazhdan's `π̃ ≅ π^ι` and `φ̃ ∈ V_π̃`). No proof is given here.
-/

noncomputable section

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The dual cusp forms lie in the contragredient** (Cogdell 2004, pp.201, 203, 206).
For every actual irreducible cuspidal operator realization `T` of `GL_(r+1)` over a number
field there is an actual irreducible cuspidal operator realization `T'` that realizes the
contragredient of `T` and contains the dual `φ̃(g) = φ(w_n ᵗg⁻¹)` of the cusp form `φ` of
every vector of `T`. -/
def CuspidalTransposeInverseContragredientStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r),
    ∃ T' : Automorphic.CuspidalOperatorRealization F r,
      Automorphic.OperatorRealization.IsContragredientOf T'.realization T.realization ∧
        ∀ x : T.Space, ∃ x' : T'.Space,
          cuspFunction F T' x' = dualFunction F (r + 1) (cuspFunction F T x)

end Langlands.Global.RankinSelbergGlobal
