import Langlands.Representation.Archimedean.ComplexJacquetRankOneReduction
import Langlands.Representation.Archimedean.ComplexGLTwoMomentJacquetProof
import Langlands.Representation.Archimedean.ComplexGLTwoMomentCompletenessProof

/-!
# The rank-one reordering of Jacquet exponents

Proof of `ComplexJacquetRankOneStatement`: the Library reduction
`complexJacquetRankOneReduction` reduces it to the `GL_2(ℂ)` statement
`ComplexGLTwoJacquetOrderingStatement`, which follows by `complexGLTwoJacquetOrderingReduction`
from the moment formulas `complexGLTwoMomentJacquet` and the moment completeness
`complexGLTwoMomentCompleteness`.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- Rank-one reordering of Jacquet exponents for irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-modules. -/
theorem complexJacquetRankOne : ComplexJacquetRankOneStatement.{uV} :=
  complexJacquetRankOneReduction.{uV}
    (complexGLTwoJacquetOrderingReduction.{uV} complexGLTwoMomentJacquet
      complexGLTwoMomentCompleteness)

end Langlands.Archimedean
