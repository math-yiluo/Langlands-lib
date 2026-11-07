import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2Continuity
import Langlands.Representation.Unitary.RightHaarHermitianApproximationStatement

/-! # Hermitian approximation of the right action on `L²([G])` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus

/-- Continuous reciprocal-Hermitian approximate identities for the right action on `L²` of the
restriction split-centre quotient `[G]` with its canonical measure. -/
def QuotientL2HermitianApproximationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
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
    ∃ (f : ℕ → AdelicGroupPoints F G → ℝ)
      (hf : ∀ n, Integrable (f n) μG.inv),
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
        (∀ a, 0 ≤ f n a) ∧ (∫ a, f n a ∂μG.inv) = 1 ∧
        ∀ a, f n a = (Measure.modularCharacter a⁻¹ : ℝ) * f n a⁻¹) ∧
      (∀ U ∈ 𝓝 (1 : AdelicGroupPoints F G),
        ∀ᶠ n in atTop, tsupport (f n) ⊆ U) ∧
      let A := fun n => rationalQuotientL2IntegratedAction F G hInv' h hi hc hT μG.inv
        (fun a => (f n a : ℂ)) (hf n).ofReal
      (∀ n, (A n).IsSymmetric ∧ ‖A n‖ ≤ 1) ∧
      (∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j), Tendsto (fun n => A n φ) atTop (𝓝 φ))

end Langlands.Global.RestrictionSplitCentre
