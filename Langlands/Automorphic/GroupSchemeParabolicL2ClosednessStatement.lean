import Langlands.Automorphic.GroupSchemeParabolicL2Period
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- Actual canonical all-parabolic periods converge on the full positive-quotient L2 space,
construct continuous tested forms, and define a closed full AE cuspidal locus. -/
def GroupSchemeParabolicL2ClosednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (_hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    (∀ (P : ProperRationalParabolic G)
      (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)),
      (∀ᵐ g ∂(Measure.haar : Measure (normOneSubgroup F G)),
        HasConvergentProperParabolicPositivePeriod F G hPD hG T i P φ g) ∧
      LocallyIntegrable (properParabolicPositivePeriod F G hPD hG T i P φ)
        (Measure.haar : Measure (normOneSubgroup F G))) ∧
    (∀ (P : ProperRationalParabolic G) (f : C_c(normOneSubgroup F G, ℂ)),
      ∃ ℓ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i) →L[ℂ] ℂ,
        ∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
          Integrable (fun g => star (f g) *
            properParabolicPositivePeriod F G hPD hG T i P φ g) Measure.haar ∧
          ℓ φ = ∫ g, star (f g) *
            properParabolicPositivePeriod F G hPD hG T i P φ g ∂Measure.haar) ∧
    IsClosed (fullAEL2CuspidalLocus F G hPD hG T i)

end Langlands.Automorphic.GroupSchemeFunctions
