import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist

/-! # Twists of cuspidal realizations by every Hecke character: proof -/

noncomputable section
universe u uP
set_option autoImplicit false

namespace Langlands.Automorphic

/-- Henniart (2000), §2.2, existence of twists by arbitrary Hecke characters: for every Hecke
character `χ`, the multiplied realization `S.heckeDeterminantTwist χ` with the twisted
presentation `P.heckeDeterminantTwist χ` is a twist of the presentation `P` of `S` by
`χ ∘ det`. -/
theorem cuspidalDeterminantMultiple : CuspidalDeterminantMultipleStatement.{u, uP} := by
  intro F _ _ _ r S P χ
  exact ⟨S.heckeDeterminantTwist χ, P.heckeDeterminantTwist χ,
    ⟨(S.realization.heckeDeterminantTwistEquiv χ).toLinearEquiv, fun _ => rfl⟩,
    fun v => ⟨((P.localComponent v).heckeDeterminantTwistRepresentationEquiv χ).trans
      (P.heckeDeterminantTwistLocalComponentEquiv χ v).symm⟩,
    P.sameEulerPolynomials_heckeDeterminantTwist χ⟩

end Langlands.Automorphic
