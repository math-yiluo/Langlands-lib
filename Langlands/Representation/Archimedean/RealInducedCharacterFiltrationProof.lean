import Langlands.Representation.Archimedean.RealInducedCharacterFiltration
import Langlands.Representation.Archimedean.RealSwapLandingIntegral
import Langlands.Representation.Archimedean.RealSwapLandingMirror

/-!
# Proof of `RealInducedCharacterFiltrationStatement`

The standard module on `GL₃(ℝ)` of an induction block `d` followed by a real character `c`,
with `Re t(d) < Re s(c)`, has the filtration `RealAdjacentFiltration 3 [] [] (induced d)
(character c)`.

`RealInducedCharacter.realInducedCharacterFiltration_of_landing` proves this from the two
halves of the landing statement, `RealSwapLandingInducedFirstStatement` and
`RealSwapLandingCharacterFirstStatement`. This module discharges both hypotheses:

* the induced-first half is `RealSwapLandingIntegral.inducedFirst`;
* the character-first half follows from it by
  `RealSwapLandingMirror.characterFirst_of_inducedFirst`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealInducedCharacterFiltrationProof

/-- **The filtration for an induction block followed by a character on `GL₃(ℝ)`.** -/
theorem realInducedCharacterFiltration : RealInducedCharacterFiltrationStatement :=
  RealInducedCharacter.realInducedCharacterFiltration_of_landing
    RealSwapLandingIntegral.inducedFirst
    (RealSwapLandingMirror.characterFirst_of_inducedFirst RealSwapLandingIntegral.inducedFirst)

end RealInducedCharacterFiltrationProof

end Langlands.Archimedean
