import Langlands.Representation.Aubert.AlternatingOperator

/-!
# Involutivity of the actual unadjusted Aubert operator

This proposition states the `GL_n` specialization of Aubert's Theorem 1.7(3)
on the exact Grothendieck group of finite-length smooth representations.
It includes rank zero and retains independent field and carrier universes.
No proof of involutivity is supplied in this statement module.
-/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The unadjusted alternating induction–Jacquet endomorphism squares to the
identity on the actual exact finite-length smooth Grothendieck group, in every
rank. This is Aubert's Theorem 1.7(3), with the block-shape sign convention of
`alternatingOperator`. -/
def InvolutivityStatement : Prop :=
  letI := T.topology
  ∀ n : ℕ,
    (alternatingOperator.{uF, uV} F T n).comp
        (alternatingOperator.{uF, uV} F T n) =
      (LinearMap.id :
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
          GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier)

end Langlands.Aubert
