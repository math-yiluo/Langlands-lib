import Langlands.Automorphic.GroupSchemeFullAEL2Integrated
import Langlands.Automorphic.GroupSchemeQuotientL2HermitianApproximationStatement

/-! # One Hermitian approximation on the original quotient and full cusp L2 spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- The same real weights approximate the identity on both original L2 spaces,
with the exact original inclusion and orthogonal projections. -/
def GroupSchemeFullAEL2HermitianApproximationStatement : Prop :=
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
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    ∃ (f : ℕ → AdelicGroupPoints F G → ℝ)
      (hf : ∀ n, Integrable (f n) μG.inv),
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
        (∀ a, 0 ≤ f n a) ∧ (∫ a, f n a ∂μG.inv) = 1 ∧
        ∀ a, f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹) ∧
      (∀ U ∈ 𝓝 (1 : AdelicGroupPoints F G),
        ∀ᶠ n in atTop, tsupport (f n) ⊆ U) ∧
      let A := fun n => haarQuotientL2IntegratedAction F G T i hi I e hc μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal
      let B := fun n => fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal
      (∀ n, (A n).IsSymmetric ∧ ‖A n‖ ≤ 1) ∧
      (∀ φ : Lp ℂ 2 μQ, Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      (∀ n, (B n).IsSymmetric ∧ ‖B n‖ ≤ 1) ∧
      (∀ ψ : S, Tendsto (fun n => B n ψ) atTop (𝓝 ψ)) ∧
      (∀ n (ψ : S), (B n ψ).val = A n ψ.val) ∧
      (∀ n (φ : Lp ℂ 2 μQ),
        fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc (A n φ) =
          B n (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ)) ∧
      (∀ n (φ : Lp ℂ 2 μQ),
        fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc (A n φ) =
          A n (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ))

end Langlands.Automorphic.GroupSchemeFunctions
