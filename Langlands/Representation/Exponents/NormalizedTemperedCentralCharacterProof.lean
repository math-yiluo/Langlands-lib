import Langlands.Representation.Exponents.NormalizedTemperedCentralCharacterStatement
import Langlands.Representation.Exponents.NormalizedTemperedSplitCentralCharacter
import Langlands.Representation.Exponents.FullCenterFromSplitComponent
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CenterSplitComponentCompactnessProof

/-! # Unitarity of central characters of nonzero normalized-exponent tempered representations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Every prescribed scalar central character of a nonzero normalized-exponent
tempered representation is unitary on the full point-group center. -/
theorem normalizedTemperedCentralCharacter :
    NormalizedTemperedCentralCharacterStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π _ ω hπ hω z
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  have hsplit := normalizedTempered_splitComponentCentralCharacter_norm
    hG a ha π ω hπ hω
  exact centralCharacter_norm_eq_one_of_splitComponent hG π ω A a ha
    (centerSplitComponentCompactness k G hG A a ha) hω hsplit z

end Langlands.Aubert.General.RepresentedParabolic
