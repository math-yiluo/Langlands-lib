import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Global.AdelicRepresentationHeight

/-! # Polynomial growth of convolution representatives on the positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

/-- For a fixed closed matrix embedding, continuous representatives of compactly
supported convolutions grow at most as a fixed power of the adelic height.
The constant depends on the weight and the bound is linear in the input norm. -/
def GroupSchemeQuotientL2ConvolutionPolynomialBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
    0 < n → IsClosedSubgroup ρ →
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    ∃ d : ℕ, ∀ (f : C_c(AdelicGroupPoints F G, ℂ)) (hf : Integrable f μG),
      ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : Lp ℂ 2 μQ,
        ∃ ψ : PositiveRationalQuotient F G T i → ℂ, Continuous ψ ∧
          (haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf φ :
            PositiveRationalQuotient F G T i → ℂ) =ᵐ[μQ] ψ ∧
          ∀ x : AdelicGroupPoints F G,
            ‖ψ (Quotient.mk _ x)‖ ≤ B * RepresentationGrowth.adelicHeight F G ρ x ^ d * ‖φ‖

end Langlands.Automorphic.GroupSchemeFunctions
