import Langlands.Global.AdelicSplitCenterMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

/-- L² membership and absolutely convergent unfolding for the existing norm-one
average on the actual positive split-centre rational adelic quotient. -/
def PositiveQuotientL2UnfoldingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (f : C_c(normOneSubgroup F G, ℂ)),
    Continuous (positiveNormOneQuotientAverage F G T i hi I e hc f) ∧
    HasCompactSupport (positiveNormOneQuotientAverage F G T i hi I e hc f) ∧
    ∃ (v : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))
      (ℓ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) →L[ℂ] ℂ),
      (v : PositiveRationalQuotient F G T i → ℂ) =ᵐ[
        positiveRationalQuotientHaarMeasure F G T i]
        positiveNormOneQuotientAverage F G T i hi I e hc f ∧
      ∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
        Integrable (fun x : normOneSubgroup F G =>
          star (f x) * φ (normOneToPositiveQuotient F G T i
            (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x))) Measure.haar ∧
        ℓ φ = inner ℂ v φ ∧
        inner ℂ v φ = ∫ x : normOneSubgroup F G,
          star (f x) * φ (normOneToPositiveQuotient F G T i
            (LeftCosetSpace.mk (rationalNormOneSubgroup F G) x)) ∂Measure.haar

end Langlands.Global.PositiveRealTorus
