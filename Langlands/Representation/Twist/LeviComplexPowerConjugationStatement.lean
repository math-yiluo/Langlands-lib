import Langlands.Representation.Twist.LeviComplexPower
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof

/-! # Complex determinant characters under actual Levi conjugation -/

noncomputable section

namespace Langlands

universe uF uV

open GeneralLinear CuspidalSupport

/-- Actual inverse Levi conjugation reindexes complex determinant exponents
by the induced bijection of blocks, and commutes with the resulting twists. -/
def LeviComplexPowerConjugationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) B C w)
    (z : Fin B.length → ℂ),
    let zC : Fin C.length → ℂ := fun j => z ((blockEquiv hw).symm j)
    (T.leviComplexPowerCharacter B z).comp
        (leviConjugation B C w hw).symm.toMonoidHom =
      T.leviComplexPowerCharacter C zC ∧
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V),
      transport B C w hw (T.leviComplexPowerTwist B z ρ) =
        T.leviComplexPowerTwist C zC (transport B C w hw ρ)

end Langlands
