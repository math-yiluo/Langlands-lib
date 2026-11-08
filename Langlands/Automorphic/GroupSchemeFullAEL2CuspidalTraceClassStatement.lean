import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Analysis.OperatorIdeals

/-! # Cuspidal trace class of convolution products from Hilbert–Schmidt convolutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- If every compactly supported continuous weight integrates the original
right action on the full almost-everywhere cuspidal space to a Hilbert–Schmidt
operator, then the Haar convolution `g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g)` of any two
such weights is integrable and integrates that action to a trace-class
operator. -/
def GroupSchemeFullAEL2CuspidalTraceClassStatement : Prop :=
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
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf)) →
    ∀ f₁ f₂ : C_c(AdelicGroupPoints F G, ℂ),
      ∃ h : Integrable (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) μG,
        Langlands.Analysis.OperatorIdeals.IsTraceClass
          (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG
            (fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG) h)

end Langlands.Automorphic.GroupSchemeFunctions
