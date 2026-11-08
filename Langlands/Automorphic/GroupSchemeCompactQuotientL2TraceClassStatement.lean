import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Analysis.OperatorIdeals

/-! # Trace-class convolution products on a compact actual quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- If the original positive rational quotient is compact, the Haar convolution
`g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g)` of two compactly supported continuous weights on
the adelic points is integrable and integrates the original right action on the
quotient `L²` to a trace-class operator. -/
def GroupSchemeCompactQuotientL2TraceClassStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    CompactSpace (PositiveRationalQuotient F G T i) →
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    ∀ f₁ f₂ : C_c(AdelicGroupPoints F G, ℂ),
      ∃ h : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) μG,
        Langlands.Analysis.OperatorIdeals.IsTraceClass
          (haarQuotientL2IntegratedAction F G T i hi I e hc μG
            (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) h)

end Langlands.Automorphic.GroupSchemeFunctions
