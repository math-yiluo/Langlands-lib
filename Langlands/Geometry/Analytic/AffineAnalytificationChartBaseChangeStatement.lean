import Langlands.Geometry.Analytic.AffineAnalytificationScalarExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension

/-! # Fixed-radius ground field comparison for affine analytification -/

universe u u' v

namespace Langlands.Analytic.AffineAnalytification

open scoped TensorProduct

/-- The chart of the algebraic base change is the scalar extension of the original
chart at the same radius, compatibly with the maps from the original algebra. -/
def AffineAnalytificationChartBaseChangeStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A : Type v) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (r : PositivePolyradius (Fin P.arity)),
    ∃ e : BoundedAlgEquiv L
      (PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L (PolynomialLocus.chart P r))
      (PolynomialLocus.chart (baseChangePresentation K L P) r),
      ∀ a : A,
        e (PresentedAffinoidAlgebra.GroundFieldExtension.iota K L (PolynomialLocus.chart P r)
          (PolynomialLocus.algebraMap P r a)) =
          PolynomialLocus.algebraMap (baseChangePresentation K L P) r ((1 : L) ⊗ₜ[K] a)

end Langlands.Analytic.AffineAnalytification
