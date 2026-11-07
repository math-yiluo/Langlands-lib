import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2InfiniteAction
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Smooth-vector density in `L²([G])` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus

/-- Archimedean smooth vectors, and vectors that are both archimedean smooth and fixed by an
open subgroup of the finite adelic points, are dense in `L²` of the restriction split-centre
quotient `[G]` with its canonical measure. -/
def QuotientL2SmoothDensityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_ : subgroup F G S j = imageSubgroup F T G i)
    (_ : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (_ : IsCentral i) (_ : IsSplitTorus T.toGrp)
    [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
    (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j)),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
    let Sm := Langlands.Archimedean.smoothVectors
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)
      (rationalQuotientL2InfiniteRightAction F G (quotientHaarMeasure F G S j) hInv')
    Dense (Sm : Set (Lp ℂ 2 (quotientHaarMeasure F G S j))) ∧
      Dense {φ : Lp ℂ 2 (quotientHaarMeasure F G S j) |
        φ ∈ Sm ∧ Langlands.IsSmoothVector
          (rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv') φ}

end Langlands.Global.RestrictionSplitCentre
