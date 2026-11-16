import Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientDuality
import Langlands.Representation.Archimedean.ComplexStandardHolomorphicGrowthProof
import Langlands.Representation.Archimedean.ComplexLinkedSmallGrowthProof
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof

/-!
# Proof: the Langlands quotient of a linked complex standard module is not large

`complexLinkedLanglandsQuotientNotLarge : ComplexLinkedLanglandsQuotientNotLargeStatement`,
assembled from the published reductions and the proofs of their inputs:

* `complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible` gives the unlinked swaps
  (`ComplexStandardUnlinkedSwapStatement`);
* `complexLinkedSmallGrowthReduction` turns them into the upper growth bound
  (`ComplexLinkedSmallGrowthStatement`);
* `complexStandardHolomorphicGrowth` is the lower growth bound
  (`ComplexStandardHolomorphicGrowthStatement`);
* `complexDualSubmoduleAnnihilator_of_growth` and
  `complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule` conclude.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- **The Langlands quotient of a linked complex standard module is not large.** -/
theorem complexLinkedLanglandsQuotientNotLarge : ComplexLinkedLanglandsQuotientNotLargeStatement :=
  complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule
    (complexDualSubmoduleAnnihilator_of_growth
      HolomorphicGrowth.complexStandardHolomorphicGrowth
      (complexLinkedSmallGrowthReduction
        (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible)))

end Langlands.Archimedean
