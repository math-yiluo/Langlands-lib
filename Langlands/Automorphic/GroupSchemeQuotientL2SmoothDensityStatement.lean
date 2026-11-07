import Langlands.Automorphic.GroupSchemeQuotientL2InfiniteAction
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Smooth-vector density on the original reductive quotient L2 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- Archimedean smooth vectors and simultaneous finite/archimedean smooth
vectors are dense in the same original canonical reductive quotient L2. -/
def GroupSchemeQuotientL2SmoothDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
    let πinf := haarQuotientL2InfiniteRightAction F G T i hi I e hc
    let S := Langlands.Archimedean.smoothVectors
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension) πinf
    Dense (S : Set (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) ∧
      Dense {φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) |
        φ ∈ S ∧ Langlands.IsSmoothVector
          (haarQuotientL2FiniteRightAction F G T i hi I e hc) φ}

end Langlands.Automorphic.GroupSchemeFunctions
