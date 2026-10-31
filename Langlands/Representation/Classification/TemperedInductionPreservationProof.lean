import Langlands.Representation.Classification.TemperedInductionPreservationStatement
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof
import Langlands.Representation.Classification.InductionWeakJacquetBoundsProof
import Langlands.Representation.Classification.TemperedExponentProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Parabolic.LeviCenterRestriction
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof

/-!
# Preservation of analytic temperedness by actual normalized GL induction

Product-Levi analytic necessity supplies the refined upper exponent bounds.
The normalized geometric lemma preserves them under actual induction, and
the ambient analytic exponent criterion supplies the conclusion.
-/

noncomputable section

namespace Langlands

universe uF uV

/-- Actual normalized upper parabolic induction preserves analytic temperedness
from an irreducible tempered representation of the standard block Levi. -/
theorem glTemperedInductionPreservation :
    GLTemperedInductionPreservationStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  dsimp only
  intro n hn B _ _ μ _ V _ _ σ hσ ht
  let := T.generalLinearTopologicalGroup n
  have hI := Parabolic.normalizedInductionAdmissibility F T B V σ ht.isAdmissible
  obtain ⟨c, _⟩ := ht.2
  let ω := c.character.comp (B.diagonalScalarToCenter F.Carrier)
  have hscalar := T.hasScalarCharacter_normalizedParabolicInduced B (ω := ω)
    (fun a v => c.acts (B.diagonalScalarToCenter F.Carrier a) v)
  apply (glTemperedExponentCriterion.{uF, max uF uV} p F T n hn _
    (T.normalizedParabolicInduced B σ) ω hI hscalar).mpr
  exact glInductionWeakJacquetBounds.{uF, uV} p F T n hn B V σ hσ ht.isAdmissible
    (glProductLeviTemperedExponentNecessity p F T n hn B μ V σ hσ ht)

end Langlands
