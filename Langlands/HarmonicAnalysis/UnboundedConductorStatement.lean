import Langlands.HarmonicAnalysis.Conductor
import Langlands.LocalField.Canonical

/-!
# Unbounded multiplicative conductors on canonical p-adic fields

An internal existence prerequisite for selecting sufficiently ramified
characters in the Rankin-Selberg arguments of JPSS 1983. The character and
conductor are the existing Library objects. This module states the
proposition; a proof is a separate obligation.
-/

namespace Langlands.HarmonicAnalysis

universe uF

/-- Every canonical p-adic field admits continuous complex quasicharacters
with multiplicative conductor at least any prescribed natural bound. -/
def PadicQuasicharacterUnboundedConductorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (A : ℕ),
    ∃ χ : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
      A ≤ F.canonicalTopologicalData.multiplicativeConductor χ

end Langlands.HarmonicAnalysis
