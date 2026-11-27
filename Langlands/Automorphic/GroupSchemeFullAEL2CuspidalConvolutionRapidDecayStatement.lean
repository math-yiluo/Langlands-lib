import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.AdelicRightConvolutionDifferentiation

/-! # Rapid decay of smooth cuspidal convolutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.InfiniteAdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

/-- On one set of reduced norm-one representatives, each smooth cuspidal
convolution and each of its archimedean orbit derivatives decay faster than
every inverse power of the height. The descended function represents the
original integrated cuspidal output. -/
def GroupSchemeFullAEL2CuspidalConvolutionRapidDecayStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]
    (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
    0 < n → IsClosedSubgroup ρ →
    let A := AdelicGroupPoints F G
    let Q := PositiveRationalQuotient F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let μG : Measure A := Measure.haar
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let mk := LeftCosetSpace.mk (positiveRationalSubgroup F G T i)
    ∃ Ω : Set A, Ω ⊆ normOneSubgroup F G ∧
      (∀ x : normOneSubgroup F G,
        ∃ r : RationalGroupPoints F G, rational F G r * x.val ∈ Ω) ∧
      ∀ (f : A → ℂ) (hf : Integrable f μG), IsAdelicTestFunction F G f → ∀ φ : S,
        let ψ := rightConvolution F G f (fun x => φ.val (mk x))
        ∃ v : C(Q, ℂ), IsAdelicSmoothFunction F G ψ ∧ (∀ x, v (mk x) = ψ x) ∧
          ((fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf φ).val :
            Q → ℂ) =ᵐ[μQ] v ∧
          ∀ (s : List (smoothModel F hG.smoothDimension)) (m : ℕ),
            ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Ω,
              ‖adelicIteratedDirectionalValue hG.smoothDimension_spec s ψ x‖ *
                RepresentationGrowth.adelicHeight F G ρ x ^ m ≤ B

end Langlands.Automorphic.GroupSchemeFunctions
