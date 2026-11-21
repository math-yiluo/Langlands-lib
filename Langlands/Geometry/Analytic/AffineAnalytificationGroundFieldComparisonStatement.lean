import Langlands.Geometry.Analytic.AffineAnalytificationScalarExtension
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas

/-! # Strong comparison of the two affine ground field extensions -/

universe u u' v

namespace Langlands.Analytic.AffineAnalytification

open Set AffinoidAtlasPresentation
open scoped TensorProduct

/-- Extension of the actual affine atlas compares to the atlas of the
algebraic base change by a full quasi-isomorphism. The comparison respects the
projection and the original coordinate algebra at every admissible pair. -/
def AffineAnalytificationGroundFieldComparisonStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] (A : Type v) [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A),
    let Q := baseChangePresentation K L P
    let S := IndexedAffinoidAtlas.GroundFieldExtension.presentation K L (atlas K P)
    let T := presentation L Q
    ∃ f : CompatibleStrongHom S T,
      f.toStrongHom.IsQuasiIso ∧
      (∀ z, baseChangeMap K L P (f.baseMap z) =
        IndexedAffinoidAtlas.GroundFieldExtension.projection K L (atlas K P) z) ∧
      ∀ (i : ChartIndex K P) (j : ChartIndex L Q)
        (h : f.baseMap '' range (S.atlas.chart i) ⊆ range (T.atlas.chart j)) (a : A),
        f.pullback i j h
          (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius L Q.arity j.val)
            ((1 : L) ⊗ₜ[K] a)) =
          PresentedAffinoidAlgebra.GroundFieldExtension.iota K L (algebra K P i.val)
            (PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity i.val) a)

end Langlands.Analytic.AffineAnalytification
