import Langlands.Automorphic.GroupSchemeFullAEL2InfiniteAction
import Langlands.Automorphic.GroupSchemeQuotientL2SmoothDensityStatement

/-! # Smooth-vector density on the original full all-parabolic cusp L2 space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- Archimedean smooth vectors and simultaneous finite/archimedean smooth
vectors are dense in the same original full all-parabolic cusp L2 space. -/
def GroupSchemeFullAEL2SmoothDensityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
    let C := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πinf := fullAEL2CuspidalInfiniteRightAction F G hPD hG T i hi I e hc
    let S := Langlands.Archimedean.smoothVectors
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension) πinf
    Dense (S : Set C) ∧
      Dense {ψ : C | ψ ∈ S ∧ Langlands.IsSmoothVector
        (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc) ψ}

end Langlands.Automorphic.GroupSchemeFunctions
