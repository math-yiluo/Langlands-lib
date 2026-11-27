import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement

/-!
# All-field port of `Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement`

Real determinant twists of actual irreducible supercuspidal GL representations.

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ

universe uF uV

/-- An actual irreducible supercuspidal representation becomes unitarizable
on its original carrier after a real power of the normalized determinant. -/
def SupercuspidalRealUnitarizationStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF}) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
        Representation.IsIrreducible ρ →
        GeneralLinear.IsSupercuspidal ρ →
        ∃ t : ℝ, IsUnitarizable (realPowerTwist (T.determinantNorm n) t ρ)

end Langlands.AllFieldBZ
