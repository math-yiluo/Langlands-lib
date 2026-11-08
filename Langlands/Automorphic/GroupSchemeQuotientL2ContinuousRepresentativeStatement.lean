import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicSplitCenterSubgroupHaar

/-! # Continuous representatives of compactly supported convolutions on the actual quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- On the original positive rational quotient, every compactly supported
continuous weight integrates the original right action to an operator whose
values are almost everywhere equal to continuous functions, with a pointwise
bound at the coset of `x` by the norm of the class, a uniform bound and the
`L¹` norm of the weight, and the positive rational subgroup measure of
`x S x⁻¹`, `S = supp f · (supp f)⁻¹`. -/
def GroupSchemeQuotientL2ContinuousRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG) (φ : Lp ℂ 2 μQ),
      ∃ ψ : PositiveRationalQuotient F G T i → ℂ, Continuous ψ ∧
        (haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf φ :
          PositiveRationalQuotient F G T i → ℂ) =ᵐ[μQ] ψ ∧
        ∀ (x : AdelicGroupPoints F G) (M : ℝ), (∀ a, ‖f a‖ ≤ M) →
          ‖ψ (Quotient.mk _ x)‖ ^ 2 ≤ M * (∫ a, ‖f a‖ ∂μG) *
            (positiveRationalSubgroupHaarMeasure F G T i hi I e hc).real
              (Subtype.val ⁻¹'
                ((fun s => x * s * x⁻¹) '' (tsupport f * (tsupport f)⁻¹))) * ‖φ‖ ^ 2

end Langlands.Automorphic.GroupSchemeFunctions
