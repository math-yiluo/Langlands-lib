import Langlands.Representation.Archimedean.RealInducedPairFiltrationReduction
import Langlands.Representation.Archimedean.RealInductionStagesFiltration
import Langlands.Representation.Archimedean.RealCharacterInducedFiltrationProof
import Langlands.Representation.Archimedean.RealInducedCharacterFiltrationProof
import Langlands.Representation.Archimedean.RealInducedInducedFiltrationProof

/-!
# Proof of `RealInducedPairFiltrationStatement`

Let `pre ++ x :: y :: post` be a list of real blocks of total rank `n`, with `x` or `y` an
induction block and `Re t(x) < Re t(y)`. Then the `O(n)`-finite functions of its standard module
have the filtration `RealAdjacentFiltration n pre post x y`.

`realInducedPairFiltration_of_base` (module `RealInducedPairFiltrationReduction`) proves this
from four statements. This module supplies a Library proof of each:

* induction in stages: `InductionStages.realAdjacentFiltrationInStages`;
* a character followed by an induction block on `GL₃(ℝ)`:
  `RealCharacterInducedFiltrationProof.realCharacterInducedFiltration`;
* an induction block followed by a character on `GL₃(ℝ)`:
  `RealInducedCharacterFiltrationProof.realInducedCharacterFiltration`;
* two induction blocks on `GL₄(ℝ)`: `realInducedInducedFiltration`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- **The adjacent filtration for a pair involving an induction block.** If `x` or `y` is an
induction block and `Re t(x) < Re t(y)`, the standard module of `pre ++ x :: y :: post` on
`GL_n(ℝ)` has the filtration `RealAdjacentFiltration n pre post x y`. -/
theorem realInducedPairFiltration : RealInducedPairFiltrationStatement :=
  realInducedPairFiltration_of_base InductionStages.realAdjacentFiltrationInStages
    RealCharacterInducedFiltrationProof.realCharacterInducedFiltration
    RealInducedCharacterFiltrationProof.realInducedCharacterFiltration
    realInducedInducedFiltration

end Langlands.Archimedean
