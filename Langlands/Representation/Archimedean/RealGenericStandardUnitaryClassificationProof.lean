import Langlands.Representation.Archimedean.RealGenericStandardUnitaryClassificationOfGeneric
import Langlands.Representation.Archimedean.RealStandardGenericProof

/-! # Proof of the real generic unitary classification on irreducible standard modules -/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- **The real generic unitary classification on irreducible standard modules.** An
irreducible infinitesimally unitary `O(n)`-finite standard module of `GLₙ(ℝ)` has a standard
parameter formed from unitary square-integrable blocks and complementary pairs of opposite
twists of such blocks by real exponents in `(0, 1/2)`. -/
theorem realGenericStandardUnitaryClassification :
    RealGenericStandardUnitaryClassificationStatement :=
  fun n ds hr hirr hunit => realGenericStandardUnitaryClassification_of_generic n ds hr hirr
    (isRealGeneric_realStandardLie n ds hr) hunit

end Langlands.Archimedean
