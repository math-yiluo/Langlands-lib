import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicRightConvolutionDifferentiation

/-! # Smooth representatives of adelic quotient convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.InfiniteAdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- Smooth test convolution of an original quotient `L²` class has a continuous
quotient representative with smooth slices and open finite level. Its actual
archimedean orbit derivatives are obtained by differentiating the test kernel. -/
def GroupSchemeQuotientL2SmoothRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (d : ℕ) (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let mk := LeftCosetSpace.mk (positiveRationalSubgroup F G T i)
    ∀ (f : AdelicGroupPoints F G → ℂ) (hf : Integrable f μG),
      IsAdelicTestFunction F G f → ∀ φ : Lp ℂ 2 μQ,
      let Φ := fun x => φ (mk x)
      let ψ := rightConvolution F G f Φ
      LocallyIntegrable Φ μG ∧
      IsAdelicSmoothFunction F G ψ ∧
      (∀ s : List (smoothModel F d),
        let k := s.foldr (rightConvolutionKernelDerivative hsmooth) f
        IsAdelicTestFunction F G k ∧ tsupport k ⊆ tsupport f ∧
          adelicIteratedDirectionalValue hsmooth s ψ = rightConvolution F G k Φ) ∧
      ∃ ψQ : C(PositiveRationalQuotient F G T i, ℂ),
        (∀ x, ψQ (mk x) = ψ x) ∧
        (haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf φ :
          PositiveRationalQuotient F G T i → ℂ) =ᵐ[μQ] ψQ

end Langlands.Automorphic.GroupSchemeFunctions
