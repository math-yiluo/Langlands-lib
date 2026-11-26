import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalSmoothTraceClassStatement

/-! # Cuspidal trace class from uniform bounds for convolution representatives -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- Uniform evaluation bounds for continuous representatives of cuspidal convolutions
imply trace class for the original operators of all adelic test functions. -/
def GroupSchemeFullAEL2CuspidalTraceClassFromUniformBoundStatement : Prop :=
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
    let Q := PositiveRationalQuotient F G T i
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let R := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG
    (∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      IsAdelicTestFunction F G f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : S, ∃ v : C(Q, ℂ),
        ((R f hf φ).val : Q → ℂ) =ᵐ[μQ] v ∧ ∀ q : Q, ‖v q‖ ≤ C * ‖φ‖) →
    ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      IsAdelicTestFunction F G f → Langlands.Analysis.OperatorIdeals.IsTraceClass (R f hf)

end Langlands.Automorphic.GroupSchemeFunctions
