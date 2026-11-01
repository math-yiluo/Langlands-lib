import Langlands.Representation.Aubert.IrreducibleImageFromEffectivity
import Langlands.Representation.Aubert.SignedEffectivityProof

/-! Actual irreducible Aubert images up to sign in every rank. -/

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The unadjusted Aubert operator sends every actual irreducible class to an
actual irreducible class or its negative. -/
theorem irreducibleImage : IrreducibleImageStatement.{uF, uV} F T :=
  irreducibleImage_of_signedEffectivity.{uF, uV} F T (signedEffectivity.{uF, uV} F T)

end Langlands.Aubert
