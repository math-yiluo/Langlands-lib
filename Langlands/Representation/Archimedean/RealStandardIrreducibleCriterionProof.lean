import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealLeviLanglandsQuotient
import Langlands.Representation.Archimedean.RealReverseIntertwinerKernel
import Langlands.Representation.Archimedean.RealLeviChartIntegrable
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealTemperedIrreducibleProof

/-!
# Speh's irreducibility criterion for `GL_n(ℝ)`, "if" direction

A proof of `Langlands.Archimedean.RealStandardIrreducibleCriterionStatement`: the Library's
reduction `realStandardIrreducibleCriterionReduction` applied to the Langlands-quotient
statement, to the unlinked swaps `realUnlinkedSwap` and to the kernel statement for
intertwiners to the reversed standard module. The first and the last are obtained from the
Levi-limit theorems `realLeviLanglandsQuotient` and `realReverseIntertwinerKernelReduction`
with their three premises: `realLeviChartIntegrable`, `realLeviParabolicIntegration` and the
irreducibility of tempered standard modules `realTemperedStandardIrreducible`. See the paired
Markdown.
-/

namespace Langlands.Archimedean

/-- **Speh's criterion, "if" direction (Mœglin 1997, Theorem 10b).** For a list `ds` of real
blocks of total rank `n` in Langlands order, if no two Mœglin data of the blocks are linked, the
`(𝔤𝔩_n(ℝ), O(n))`-module of `O(n)`-finite functions of the standard module of `ds` is
irreducible. -/
theorem realStandardIrreducibleCriterion : RealStandardIrreducibleCriterionStatement :=
  realStandardIrreducibleCriterionReduction
    (realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration
      realTemperedStandardIrreducible)
    realUnlinkedSwap
    (realReverseIntertwinerKernelReduction realLeviChartIntegrable realLeviParabolicIntegration
      realTemperedStandardIrreducible)

end Langlands.Archimedean
