import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Langlands.Automorphic.GroupSchemeNormOneSmooth
import Langlands.Global.AdelicSplitCenterQuotient

/-! # Smooth slices on the quotient by the positive split centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj ContDiff Manifold

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints InfiniteAdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- The projection along the split positive centre is smooth on infinite points.
Smoothness on the norm-one fibres is equivalent to plot-smoothness of the
pullback on each infinite slice of the full adelic group. -/
def GroupSchemePositiveQuotientSmoothnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    {d m : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (A : NormOneLieAtlas F G hsmooth m)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i),
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    let p := normOneProjection F G T i hi I e hc
    ∃ pInf : InfiniteAdelicGroupPoints F G → infiniteNormOneSubgroup F G,
      (∀ a, infiniteNormOneInclusion F G (pInf a) = p (ofInfinite F G a)) ∧
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, Fin m → ℝ) ∞ pInf ∧
      ∀ f : normOneSubgroup F G → ℂ,
        (∀ b : FiniteAdelicGroupPoints F G,
          (fun a => f (p (pair F G a b))) ∈ InfinitePlotSmoothFunctions F G) ↔
        ∀ x, ContMDiff 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, ℂ) ∞ (normOneInfiniteSlice F G f x)

end Langlands.Automorphic.GroupSchemeFunctions
