import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Twist.LeviRealPower
import Langlands.Representation.Unitary.Basic

/-!
# Real unitarization of irreducible cuspidal product-Levi representations

Every irreducible cuspidal representation of an actual standard product Levi
of `GL_n` becomes unitarizable after the real determinant twist
`∏ᵢ |det mᵢ|^(tᵢ)` for some real exponent vector `t`. This is a proposition
definition, not a proof.
-/

namespace Langlands

open GeneralLinear

universe uF uV

/-- Every irreducible admissible quasicuspidal representation of an actual
standard product Levi has a real determinant twist, with exponent `+t`, that
carries an invariant positive definite Hermitian form on the original
carrier. -/
def LeviCuspidalRealUnitarizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (D : BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (D.Levi F.Carrier) V),
      Representation.IsIrreducible ρ →
      CuspidalSupport.IsLeviCuspidal D ρ →
      ∃ t : Fin D.length → ℝ, IsUnitarizable (T.leviRealPowerTwist D t ρ)

end Langlands
