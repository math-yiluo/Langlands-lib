import Langlands.Automorphic.GroupSchemeFullAEL2InfiniteAction
import Langlands.Automorphic.GroupSchemeFullAEL2ContinuousCuspidality
import Langlands.Global.AdelicMaximalUnipotentDecay
import Langlands.Global.AdelicRepresentationHeight
import Langlands.Global.InfiniteAdelicLinearRealization
import Langlands.Representation.Archimedean.SmoothVectors

/-! # Rapid decay of smooth vectors in the full cuspidal Hilbert space -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
  Langlands.Global.InfiniteAdelicGroupPoints Langlands.Global.PositiveRealTorus
  Langlands.GroupScheme

universe u

/-- A finite-level, archimedean smooth cuspidal Hilbert vector has a smooth
pointwise cuspidal representative with all-word rapid decay on a common
reduced cover of the norm-one quotient. -/
def GroupSchemeFullAEL2SmoothCuspidalRapidDecayStatement : Prop :=
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
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    let A := AdelicGroupPoints F G
    let Q := PositiveRationalQuotient F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let mk := LeftCosetSpace.mk (positiveRationalSubgroup F G T i)
    ∃ Ω : Set A, Ω ⊆ normOneSubgroup F G ∧
      (∀ x : normOneSubgroup F G,
        ∃ r : RationalGroupPoints F G, rational F G r * x.val ∈ Ω) ∧
      ∀ φ : S,
        Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, smoothModel F hG.smoothDimension)
          (fullAEL2CuspidalInfiniteRightAction F G hPD hG T i hi I e hc) φ →
        IsSmoothVector (fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc) φ →
        ∃ v : C(Q, ℂ), (φ.val : Q → ℂ) =ᵐ[μQ] v ∧
          IsAdelicSmoothFunction F G (v ∘ mk) ∧
          positiveQuotientContinuousPullback F G T i v ∈
            normalizedParabolicCuspidalSubrepresentation F G hPD hG ∧
          ∀ (s : List (smoothModel F hG.smoothDimension)) (m : ℕ),
            ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Ω,
              ‖adelicIteratedDirectionalValue hG.smoothDimension_spec s (v ∘ mk) x‖ *
                RepresentationGrowth.adelicHeight F G ρ x ^ m ≤ B

end Langlands.Automorphic.GroupSchemeFunctions
