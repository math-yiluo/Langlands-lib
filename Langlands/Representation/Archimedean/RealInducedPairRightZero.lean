import Langlands.Representation.Archimedean.RealInducedCharacterFiltration
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealInducedInducedNonzeroReduction

/-!
# Filtration when the right induction block has weight zero

The proved landing inputs close the induced-character case. Induction in
stages and zero-weight fusion give the two-induced-block filtration with
arbitrary surroundings and no linking restriction.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairRightZero

/-- A block of weight zero on the right admits the actual adjacent filtration,
with arbitrary surrounding lists, at every strictly ascending exponent gap. -/
theorem filtration (n : ℕ) (pre post : List RealBlock)
    (d e : ComplexCharacterData) (he : e.weight = 0)
    (hrank : realRank (pre ++ .induced d :: .induced e :: post) = n)
    (hlt : realBlockExponent (.induced d) < realBlockExponent (.induced e)) :
    RealAdjacentFiltration n pre post (.induced d) (.induced e) := by
  have hIC : RealInducedCharacterFiltrationStatement :=
    RealInducedCharacter.realInducedCharacterFiltration_of_landing
      RealSwapLandingIntegral.inducedFirst
      (RealSwapLandingMirror.characterFirst_of_inducedFirst
        RealSwapLandingIntegral.inducedFirst)
  exact RealInducedInducedNonzeroReduction.right_zero hIC n pre post d e he hrank hlt

end RealInducedPairRightZero

/-- The adjacent filtration with a zero-weight right induction block, in every
ambient rank and with arbitrary surrounding lists. -/
def RealInducedPairRightZeroFiltrationStatement : Prop :=
  ∀ (n : ℕ) (pre post : List RealBlock) (d e : ComplexCharacterData),
    e.weight = 0 →
      realRank (pre ++ .induced d :: .induced e :: post) = n →
        realBlockExponent (.induced d) < realBlockExponent (.induced e) →
          RealAdjacentFiltration n pre post (.induced d) (.induced e)

theorem realInducedPairRightZeroFiltration : RealInducedPairRightZeroFiltrationStatement :=
  RealInducedPairRightZero.filtration

end Langlands.Archimedean
