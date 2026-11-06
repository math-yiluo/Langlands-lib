import Langlands.GroupScheme.Absolute.RootVectorLineStructuralAssembly
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Actual absolute root subgroups are vector groups of dimension one: proof -/

universe u

namespace Langlands.GroupScheme

/-- For a split maximal torus of a connected reductive group over an
algebraically closed field, each intrinsic root functor has an actual closed
representative which is a vector group of dimension one. -/
theorem absoluteRootVectorLine : AbsoluteRootVectorLineStatement.{u} :=
  absoluteRootVectorLineStructuralReduction solvableProperFixedPoint
    solvableTorusQuotient dynamicCentralizerReductive

end Langlands.GroupScheme
