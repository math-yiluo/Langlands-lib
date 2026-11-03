import Langlands.GroupScheme.Rational.CoordinateCotangentSupportProof

/-! # Actual augmentation cotangent and Lie-kernel weight comparison -/

universe u

namespace Langlands.GroupScheme.CoordinateWeights

/-- The actual kernel duality, direct action pairing and intrinsic weight-support
comparison, over every field and at every universe. -/
theorem coordinateLieComparison : CoordinateLieComparisonStatement.{u} :=
  ⟨kernelCotangentDuality, cotangentActionPairing, cotangentLieSupport⟩

end Langlands.GroupScheme.CoordinateWeights
