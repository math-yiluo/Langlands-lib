import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismCompatibility
import Langlands.Geometry.Analytic.SchemeAnalytificationBasicOpenRangeProof

/-! # Center and rational-point compatibility for scheme analytification maps -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.MorphismCompatibility

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']

/-- Every analytification map commutes with centers and sends analytic rational
points to the analytic points of their algebraic images. -/
theorem compatibility (g : X ⟶ Y) (hg : g ≫ f' = f)
    (F : C(Space K f, Space K f')) (hF : IsAnalytificationMap K f f' g hg F) :
    (∀ z : Space K f, center K f' (F z) = g (center K f z)) ∧
      ∀ p : RingPoint K (Over.mk f) K,
        F (analyticRationalPoint K f p) =
          analyticRationalPoint K f' (p ≫ Over.homMk g hg) :=
  compatibility_of_range_and_seminorm_injective K f f'
    (OpenGluing.range_ι K f) (OpenGluing.range_ι K f')
    (fun V => AffineAnalytification.SeminormComparison.pointSeminorm_injective K
      (chartPresentation K f' V))
    g hg F hF

end Langlands.Analytic.SchemeAnalytification.MorphismCompatibility
