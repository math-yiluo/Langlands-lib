import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylReduction
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerRootGeneration

/-! # The full simply connected normalizer image over the maximal unramified extension -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The full original normalizer image is the affine Weyl group for every supplied
building datum of a simply connected group over the actual inertia fixed field. -/
theorem simplyConnectedNormalizerAffineWeyl :
    SimplyConnectedNormalizerAffineWeylStatement.{u} :=
  simplyConnectedNormalizerAffineWeyl_of_quasiSplitRootGeneration
    Langlands.GroupScheme.quasiSplitSimplyConnectedRootGeneration

end Langlands.Geometry.Building.MaximalUnramified
