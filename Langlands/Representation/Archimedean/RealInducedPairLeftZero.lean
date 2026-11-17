import Langlands.Representation.Archimedean.RealCharacterInducedFiltration
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealOrthogonalUncertainty
import Langlands.Representation.Archimedean.RealInducedInducedNonzeroReduction

/-!
# Filtration when the left induction block has weight zero

The proved landing and uncertainty inputs close the character-induced case.
Its induction in stages and zero-weight fusion give the two-induced-block
filtration with arbitrary surroundings and no linking restriction.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairLeftZero

/-- A block of weight zero on the left admits the actual adjacent filtration,
with arbitrary surrounding lists, at every strictly ascending exponent gap. -/
theorem filtration (n : ℕ) (pre post : List RealBlock)
    (d e : ComplexCharacterData) (hd : d.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e)) :
    RealAdjacentFiltration n pre post (.induced d) (.induced e) := by
  have hCI : RealCharacterInducedFiltrationStatement :=
    RealCharacterInducedFiltration.realCharacterInducedFiltration_of
      ⟨RealSwapLandingIntegral.inducedFirst,
        RealSwapLandingMirror.characterFirst_of_inducedFirst
          RealSwapLandingIntegral.inducedFirst⟩
      RealOrthogonalUncertainty.realOrthogonalBlockUncertainty
  exact RealInducedInducedNonzeroReduction.left_zero hCI n pre post d e hd hrank hlt

end RealInducedPairLeftZero

/-- The adjacent filtration with a zero-weight left induction block, in every
ambient rank and with arbitrary surrounding lists. -/
def RealInducedPairLeftZeroFiltrationStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData),
    d.weight = 0 →
      realRank (pre ++ .induced d :: .induced e :: post) = n →
        realBlockExponent (.induced d) < realBlockExponent (.induced e) →
          RealAdjacentFiltration n pre post (.induced d) (.induced e)

theorem realInducedPairLeftZeroFiltration : RealInducedPairLeftZeroFiltrationStatement :=
  RealInducedPairLeftZero.filtration

end Langlands.Archimedean
