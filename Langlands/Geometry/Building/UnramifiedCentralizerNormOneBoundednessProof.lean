import Langlands.Geometry.Building.UnramifiedCentralizerNormOneBoundednessReduction
import Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof

/-! # Algebraic boundedness of the norm-one unramified centralizer -/

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The norm-one subgroup of the supplied maximal-split-torus centralizer over the
actual maximal unramified field has algebraically bounded image. -/
theorem centralizerNormOneBounded : CentralizerNormOneBoundedStatement.{u} :=
  centralizerNormOneBounded_of_henselianDiscreteQuasiSplit
    (Langlands.GroupScheme.henselianDiscreteQuasiSplit_of_dimensionLEOne
      Langlands.GroupScheme.dimensionLEOneQuasiSplit)

end Langlands.Geometry.Building.MaximalUnramified
