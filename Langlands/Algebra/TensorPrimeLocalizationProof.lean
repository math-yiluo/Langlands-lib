import Langlands.Algebra.TensorPrimeLocalizationStatement
import Langlands.Algebra.PrimeLocalizationCriterion

universe u v w x y z

namespace Langlands.Algebra

/-- The actual tensor transition is a prime localization. -/
theorem tensorPrimeLocalization :
    TensorPrimeLocalizationStatement.{u, v, w, x, y, z} :=
  @isLocalization_atPrime_tensor_of_isPushout.{u, v, w, x, y, z}

end Langlands.Algebra
