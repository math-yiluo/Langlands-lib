import Langlands.AllFieldBZ.Representation.Twist.LeviRealPower
import Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement

/-!
# All-field port of `Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement`

Every irreducible cuspidal representation of an actual standard product Levi
of `GL_n` becomes unitarizable after the real determinant twist
`∏ᵢ |det mᵢ|^(tᵢ)` for some real exponent vector `t`. This is a proposition
definition, not a proof.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ

open Langlands.GeneralLinear

universe uF uV

/-- Every irreducible admissible quasicuspidal representation of an actual
standard product Levi has a real determinant twist, with exponent `+t`, that
carries an invariant positive definite Hermitian form on the original
carrier. -/
def LeviCuspidalRealUnitarizationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (D : BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (D.Levi F.Carrier) V),
      Representation.IsIrreducible ρ →
      CuspidalSupport.IsLeviCuspidal D ρ →
      ∃ t : Fin D.length → ℝ, IsUnitarizable (T.leviRealPowerTwist D t ρ)

end Langlands.AllFieldBZ
