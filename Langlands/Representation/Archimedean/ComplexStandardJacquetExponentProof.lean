import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentRoute
import Langlands.Representation.Archimedean.ComplexJacquetCasselmanOsborneProof
import Langlands.Representation.Archimedean.ComplexJacquetTranslationProof
import Langlands.Representation.Archimedean.ComplexJacquetAntidominantBoundProof

/-!
# The exponent shape of Jacquet functionals on complex principal series

`complexStandardJacquetExponent : ComplexStandardJacquetExponentStatement`, from the route
`complexStandardJacquetExponentRoute : CO → Trans → Bound → JE` and the proofs of its three
inputs.
-/

namespace Langlands.Archimedean

/-- **Exponents of Jacquet functionals of complex principal series.** -/
theorem complexStandardJacquetExponent : ComplexStandardJacquetExponentStatement :=
  complexStandardJacquetExponentRoute complexJacquetCasselmanOsborne complexJacquetTranslation
    complexJacquetAntidominantBound

end Langlands.Archimedean
