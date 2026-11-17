import Langlands.Representation.Archimedean.RealStandardCentralGrowth
import Langlands.Representation.Archimedean.RealLeftPolynomialGrowthProof
import Langlands.Representation.Archimedean.RealTaylorLeftPolynomialProof
import Langlands.Representation.Archimedean.RealPairLinkedJacquetFunctionalProof
import Langlands.Representation.Archimedean.RealLinkedJacquetInStagesProof
import Langlands.Representation.Archimedean.RealSwapSurjectiveProof
import Langlands.Representation.Archimedean.RealCharacterSwapProof
import Langlands.Representation.Archimedean.RealCharacterInducedUnlinked
import Langlands.Representation.Archimedean.RealInducedCharacterUnlinked
import Langlands.Representation.Archimedean.RealInducedSwapUnlinked

/-!
# Langlands quotients with a linked pair are not maximally faithful

This module proves `RealLinkedLanglandsQuotientNotLargeStatement` (module
`RealLargeStandardIrreducibleReduction`). The proof assembles proved Library theorems:

* `realUnlinkedSwap`: the swap of two adjacent unlinked blocks (`RealUnlinkedSwapStatement`),
  from the Library reduction `realUnlinkedSwapReduction` and its four proved cases;
* `realLinkedJacquetFunctional`: a linked Langlands-ordered list carries a nonzero Jacquet
  functional killed by a power of a lower root vector (`RealLinkedJacquetFunctionalStatement`),
  from the Library reduction `realLinkedJacquetFunctionalReduction`;
* `realLinkedLanglandsQuotientNotLarge`: the target, from the growth comparison of module
  `RealStandardCentralGrowth` and the split of module `RealLinkedJacquetFunctional`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

/-- **Unlinked swap.** Two adjacent unlinked real blocks, the first of larger or equal real
exponent, can be exchanged by an injective `(𝔤, K)`-intertwiner. The four kinds of pairs are the
proved Library theorems for two characters, a character and an induction block (both orders), and
two induction blocks. -/
theorem realUnlinkedSwap : RealUnlinkedSwapStatement :=
  realUnlinkedSwapReduction RealCharacterSwap.realCharacterSwap realCharacterInducedSwap
    realInducedCharacterSwap realInducedSwap

/-- **Linked Jacquet functional (S2).** From the Library reduction
`realLinkedJacquetFunctionalReduction`: induction in stages, unlinked swaps, surjectivity of
swap intertwiners, and the case of two linked blocks. -/
theorem realLinkedJacquetFunctional : RealLinkedJacquetFunctionalStatement :=
  realLinkedJacquetFunctionalReduction realLinkedJacquetFunctionalInStages realUnlinkedSwap
    realSwapInjectiveIntertwinerSurjective realPairLinkedJacquetFunctional

/-- **The Langlands quotient of a Langlands-ordered real standard module with a linked pair of
Mœglin data is not maximally faithful.** The growth bound `RealLinkedQuotientGrowthStatement`
follows from S1 (`realLeftPolynomialGrowth`), S3 (`realTaylorLeftPolynomial`) and S2
(`realLinkedJacquetFunctional`); the growth comparison then gives the target. -/
theorem realLinkedLanglandsQuotientNotLarge : RealLinkedLanglandsQuotientNotLargeStatement :=
  realLinkedLanglandsQuotientNotLarge_of_quotientGrowth
    (realLinkedQuotientGrowth_of_split realLeftPolynomialGrowth realTaylorLeftPolynomial
      realLinkedJacquetFunctional)

end Langlands.Archimedean
