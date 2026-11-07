import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2Continuity

/-! # Hermitian approximation of the right action on the a.e. cuspidal subspace of `L²([G])` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

/-- One sequence of continuous reciprocal-Hermitian approximate identities on `G(𝔸)` whose
integrated actions approximate the identity on `L²([G])` and on its almost-everywhere cuspidal
subspace, compatibly with the inclusion and the orthogonal projections. -/
def QuotientFullAEL2HermitianApproximationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (h : subgroup F G S j = imageSubgroup F T G i)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
    (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j)),
    let μG : Measure (AdelicGroupPoints F G) := Measure.haar
    let Sq := quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
    ∃ (f : ℕ → AdelicGroupPoints F G → ℝ)
      (hf : ∀ n, Integrable (f n) μG.inv),
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
        (∀ a, 0 ≤ f n a) ∧ (∫ a, f n a ∂μG.inv) = 1 ∧
        ∀ a, f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹) ∧
      (∀ U ∈ 𝓝 (1 : AdelicGroupPoints F G),
        ∀ᶠ n in atTop, tsupport (f n) ⊆ U) ∧
      let A := fun n => rationalQuotientL2IntegratedAction F G hInv' h hi hc hT μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal
      let B := fun n => quotientFullAEL2CuspidalIntegratedAction F G hPD hG h hi hc hT hInv'
        μG.inv (fun a => (f n a : ℂ)) (hf n).ofReal
      (∀ n, (A n).IsSymmetric ∧ ‖A n‖ ≤ 1) ∧
      (∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j), Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      (∀ n, (B n).IsSymmetric ∧ ‖B n‖ ≤ 1) ∧
      (∀ ψ : Sq, Tendsto (fun n => B n ψ) atTop (𝓝 ψ)) ∧
      (∀ n (ψ : Sq), (B n ψ).val = A n ψ.val) ∧
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT (A n φ) =
          B n (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ)) ∧
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT (A n φ) =
          A n (quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ))

end Langlands.Global.RestrictionSplitCentre
