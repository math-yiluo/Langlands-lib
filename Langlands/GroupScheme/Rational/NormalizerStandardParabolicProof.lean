import Langlands.GroupScheme.Rational.NormalizerParabolicPoints
import Langlands.GroupScheme.Rational.TitsStandardParabolicStatement

/-! # A normalizing point lies in `P_J(k)` exactly when its class lies in `W_J` -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- A normalizing point lies in the standard parabolic `P_J(k)` exactly when its class lies in
`W_J` (Borel–Tits 5.15, 5.17). -/
theorem normalizerStandardParabolicStatement : NormalizerStandardParabolicStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro _ J _ n
  exact ⟨hi.isSplitSubtorus.mk_mem_standardRelativeWeylGroup ν J,
    coe_mem_standardParabolicPoints_of_mk_mem i ν J⟩

end Langlands.GroupScheme
