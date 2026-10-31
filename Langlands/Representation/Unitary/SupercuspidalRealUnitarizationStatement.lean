import Langlands.Representation.Classification.Supercuspidal
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.Twist.RealPower

/-! Real determinant twists of actual irreducible supercuspidal GL representations. -/

namespace Langlands

universe uF uV

/-- An actual irreducible supercuspidal representation becomes unitarizable
on its original carrier after a real power of the normalized determinant. -/
def SupercuspidalRealUnitarizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
        Representation.IsIrreducible ρ →
        GeneralLinear.IsSupercuspidal ρ →
        ∃ t : ℝ, IsUnitarizable (realPowerTwist (T.determinantNorm n) t ρ)

end Langlands
