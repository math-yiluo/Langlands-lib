import Langlands.HarmonicAnalysis.UnboundedConductorStatement
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
/-!
# Unbounded multiplicative conductors on canonical p-adic fields

An internal existence prerequisite for selecting sufficiently ramified
characters in the Rankin-Selberg arguments of JPSS 1983. The character and
conductor are the existing Library objects. This module states the
proposition; a proof is a separate obligation.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicQuasicharacterUnboundedConductorStatement
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Every canonical p-adic field admits continuous complex quasicharacters
with multiplicative conductor at least any prescribed natural bound. -/
def PadicQuasicharacterUnboundedConductorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (A : ℕ),
    ∃ χ : (Quasicharacter F),
      A ≤ (⟨⟩ : LocalFieldData F).multiplicativeConductor χ

end Langlands.AllField.HarmonicAnalysis
