import Langlands.Representation.Archimedean.ComplexStandardHomExponentJacquetReduction
import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentProof

/-!
# The exponent shape of intertwinings between complex principal series

`complexStandardHomExponent : ComplexStandardHomExponentStatement`, from the reduction
`complexStandardHomExponentJacquetReduction : JE → E` and the proof
`complexStandardJacquetExponent` of JE.
-/

namespace Langlands.Archimedean

/-- **Exponents of intertwinings between complex principal series.** A nonzero
`(𝔤, K)`-module map `X(d) → X(c)` forces `c_j` to be `d_{σ j}` shifted by `(u_j + v_j)/2` in the
exponent and by `u_j - v_j` in the weight, for a permutation `σ` and nonnegative integer
combinations `u`, `v` of the simple roots. -/
theorem complexStandardHomExponent : ComplexStandardHomExponentStatement :=
  complexStandardHomExponentJacquetReduction complexStandardJacquetExponent

end Langlands.Archimedean
