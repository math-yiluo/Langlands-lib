import Langlands.Geometry.Analytic.DistinguishedNormalization
import Langlands.Geometry.Analytic.WeierstrassStatement

/-! # Analytic Weierstrass division and preparation -/

universe u

namespace Langlands.Analytic.RestrictedSeries

variable (A : Type u) [NormedCommRing A] [IsUltrametricDist A]
  [Nontrivial A] [NormOneClass A] [NormMulClass A] [CompleteSpace A]

theorem weierstrass : WeierstrassStatement A :=
  ⟨fun f d hf g => existsUnique_distinguished_division f d hf g,
    fun f d hf => existsUnique_distinguished_preparation f d hf⟩

end Langlands.Analytic.RestrictedSeries
