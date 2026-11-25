import Langlands.Automorphic.GroupSchemeQuotientL2
import Langlands.TraceFormula.TwistedOrbital

/-!
# Covariance of the twisting operator with right translation

For an automorphism `Θ` of `G(𝔸_F)` preserving the positive rational subgroup `Γ`, with
`(Θ̄)⁻¹` measure preserving on `Γ \ G(𝔸_F)`, the twisting operator `I_Θ φ = φ ∘ Θ̄⁻¹` and the
right translations `R(a)` on `L²(Γ \ G(𝔸_F))` satisfy `I_Θ (R(a) φ) = R(Θ a) (I_Θ φ)`
(`twistOperator_quotientL2RightTranslate`): both sides are `φ ∘ (Γx ↦ Γ Θ⁻¹(x) a)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.PositiveRealTorus Langlands.Global.AdelicGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

namespace Langlands.TraceFormula.IsotypicTrace

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
variable (measureQ : Measure (PositiveRationalQuotient F G T i))
  (hInvariant : QuotientMeasureRightInvariant F G T i measureQ)

/-- **Covariance.** `I_Θ ∘ R(a) = R(Θ a) ∘ I_Θ` on the quotient `L²` space. -/
theorem twistOperator_quotientL2RightTranslate
    (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
    (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔ x ∈ positiveRationalSubgroup F G T i)
    (hΘμ : MeasurePreserving
      (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm measureQ measureQ)
    (a : AdelicGroupPoints F G) (φ : Lp ℂ 2 measureQ) :
    twistOperator (positiveRationalSubgroup F G T i) Θ hΘ measureQ hΘμ
        (quotientL2RightTranslate F G T i measureQ hInvariant a φ) =
      quotientL2RightTranslate F G T i measureQ hInvariant (Θ a)
        (twistOperator (positiveRationalSubgroup F G T i) Θ hΘ measureQ hΘμ φ) := by
  let Γ := positiveRationalSubgroup F G T i
  let q := (quotientAutomorphism Γ Θ hΘ).symm
  have key : ∀ (f f' : PositiveRationalQuotient F G T i → PositiveRationalQuotient F G T i)
      (h : f = f') (hf : MeasurePreserving f measureQ measureQ)
      (hf' : MeasurePreserving f' measureQ measureQ),
      Lp.compMeasurePreserving f hf φ = Lp.compMeasurePreserving f' hf' φ := by
    intro f f' h hf hf'
    subst h
    rfl
  change Lp.compMeasurePreserving q hΘμ
      (Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ a) (hInvariant a) φ) =
    Lp.compMeasurePreserving (LeftCosetSpace.rightTranslate Γ (Θ a)) (hInvariant (Θ a))
      (Lp.compMeasurePreserving q hΘμ φ)
  rw [← Lp.compMeasurePreserving_comp_apply, ← Lp.compMeasurePreserving_comp_apply]
  apply key
  funext x
  induction x using Quotient.inductionOn with
  | _ x =>
    change LeftCosetSpace.rightTranslate Γ a (q (LeftCosetSpace.mk Γ x)) =
      q (LeftCosetSpace.rightTranslate Γ (Θ a) (LeftCosetSpace.mk Γ x))
    rw [LeftCosetSpace.rightTranslate_mk]
    change LeftCosetSpace.rightTranslate Γ a (LeftCosetSpace.mk Γ (Θ.symm x)) =
      LeftCosetSpace.mk Γ (Θ.symm (x * Θ a))
    rw [LeftCosetSpace.rightTranslate_mk, map_mul, ContinuousMulEquiv.symm_apply_apply]

end Langlands.TraceFormula.IsotypicTrace
