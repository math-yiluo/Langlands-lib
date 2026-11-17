import Langlands.Representation.Archimedean.RealCharacterInducedFiltration
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror
import Langlands.Representation.Archimedean.RealOrthogonalUncertainty

/-!
# Proof of `RealCharacterInducedFiltrationStatement`

The standard module on `GL₃(ℝ)` of a real character `c` followed by an induction block `d`,
with `Re s(c) < Re t(d)`, has the filtration `RealAdjacentFiltration 3 [] [] (character c)
(induced d)`.

`RealCharacterInducedFiltration.realCharacterInducedFiltration_of` proves this from the landing
statement `RealSwapLandingStatement` and the uncertainty statement
`RealOrthogonalBlockUncertaintyStatement`. This module discharges both hypotheses:

* the induced-first half of the landing statement is
  `RealSwapLandingIntegral.inducedFirst`;
* the character-first half follows from it by `RealSwapLandingMirror.characterFirst_of_inducedFirst`;
* the uncertainty statement is `RealOrthogonalUncertainty.realOrthogonalBlockUncertainty`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealCharacterInducedFiltrationProof

/-- The landing statement for block multiplier composites on `GL₃(ℝ)`: the induced-first half
is proved analytically, and the character-first half is its mirror image. -/
theorem realSwapLanding : RealSwapLandingStatement :=
  ⟨RealSwapLandingIntegral.inducedFirst,
    RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst⟩

/-- **The filtration for a character followed by an induction block on `GL₃(ℝ)`.** -/
theorem realCharacterInducedFiltration : RealCharacterInducedFiltrationStatement :=
  RealCharacterInducedFiltration.realCharacterInducedFiltration_of realSwapLanding
    RealOrthogonalUncertainty.realOrthogonalBlockUncertainty

end RealCharacterInducedFiltrationProof

end Langlands.Archimedean
