import Langlands.Representation.Parabolic.SecondAdjointnessAssembly
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Parabolic.NaturalJacquetDualityProof

/-!
# Natural normalized second adjointness

For standard parabolics of `GL_n` and for refined parabolics of product Levis,
normalized parabolic induction is naturally left adjoint to the opposite
normalized Jacquet functor on admissible representations.
-/

namespace Langlands.Parabolic

universe uF uV uW

/-- Natural normalized second adjointness, standard and refined. -/
theorem normalizedSecondAdjointness :
    NormalizedSecondAdjointnessStatement.{uF, uV, uW} :=
  SecondAdjointness.secondAdjointness_of_dualities
    naturalNormalizedInductionDuality.{uF, uV}
    naturalNormalizedJacquetDuality.{uF, uW}

end Langlands.Parabolic
