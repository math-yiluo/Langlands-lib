import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Analysis.OperatorIdeals

/-!
# Trace class on the full automorphic `L²` space

This proposition is derived from the cuspidal operator arguments in Getz–Hahn (2024),
Theorem 9.1.2, Lemma 16.4.2, Theorem 18.2.5 and §18.5. Its setting and provenance are
described in `GroupSchemeFullL2TraceClassStatement.md`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions

namespace Langlands.TraceFormula

/-- If `f₁` and `f₂` are compactly supported continuous weights that each integrate the right
action on the full almost-everywhere cuspidal space to a Hilbert–Schmidt operator, and `f₂`
integrates to zero along every two-sided translate of the adelic points of the unipotent
radical of every proper rational parabolic, then the Haar convolution
`g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g)` is integrable and integrates the right action on the whole
`L²` space of the positive rational quotient to a trace-class operator. -/
def GroupSchemeFullL2TraceClassStatement : Prop :=
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
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    ∀ f₁ f₂ : C_c(AdelicGroupPoints F G, ℂ),
      (∀ h₁ : Integrable f₁ μG, Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG, Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic G) (x y : AdelicGroupPoints F G),
        ∫ n, f₂ (x * (n : AdelicGroupPoints F G) * y)
          ∂properParabolicHaarMeasure F G hPD hG P = 0) →
      ∃ h : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) μG,
        Langlands.Analysis.OperatorIdeals.IsTraceClass
          (haarQuotientL2IntegratedAction F G T i hi I e hc μG
            (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) h)

end Langlands.TraceFormula
