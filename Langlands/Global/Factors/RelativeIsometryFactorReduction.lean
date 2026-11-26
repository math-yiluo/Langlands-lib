import Langlands.Global.Factors.RelativePairEpsilonCanonical
import Langlands.Global.Factors.RelativePairEpsilonScaling

/-!
# Relative isometry factors from the tempered pair comparison

The witnessed local supports give the temperedness needed for Henniart's
Corollary 2.3. Multiplicativity, together with the change of additive character
and the determinant identity, gives the compatibility on the generated span.
-/

noncomputable section

set_option autoImplicit false

universe uF uW uP uE

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassFieldTheory.Global

/-- The witnessed relative factor statement follows from the tempered comparison
at the presentation, Weil, and local-constant universes used by the witnesses. -/
def RelativeIsometryFactorReductionStatement : Prop :=
  RelativeWeilGroup.AssociatedTemperedFactorStatement.{uF, uW, uP, uP, uE} →
    RelativeIsometryFactorStatement.{uF, uW, uP, uE}

/-- Henniart's Corollary 2.3 implies the relative determinant and pair-factor
compatibility of Proposition 2.6. -/
theorem relativeIsometryFactorStatement_of_tempered :
    RelativeIsometryFactorReductionStatement.{uF, uW, uP, uE} := by
  intro hcomparison F E _ _ _ _ _ _ _ c hc v _ _ T hT
  refine ⟨fun e he => relativeIsometryDeterminantCompatibility F E c v hc T hT e he,
    fun ψ => ⟨⟨Correspondence.localSelfDualHaar (padicField v) ψ,
      Correspondence.isSelfDual_localSelfDualHaar (padicField v) ψ⟩, fun ν hν x y => ?_⟩⟩
  refine ⟨relativePairLFactor_of_witnessed F E c v T hT ψ ν hν
    (witnessed_isUnitaryPairLFactor F E c v hc hcomparison ψ ν hν) x y, fun eC ε hε => ?_⟩
  obtain ⟨e, hW, hG⟩ := relativePairEpsilon_canonical F E c v hc hcomparison T hT eC ε hε x y
  exact relativePairEpsilonScaling F E c v hc T hT _ ψ _ ν
    (Correspondence.isSelfDual_localSelfDualHaar (padicField v) (canonicalLocalCharacter F v))
    hν eC ε hε x y e hW hG

end Langlands.Global.PoleComparison
