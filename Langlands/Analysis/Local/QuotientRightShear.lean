import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! # Right translation in the quotient variable of a product measure -/

noncomputable section

open MeasureTheory Topology

namespace Langlands.QuotientIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_rightTranslate_joint (H : Subgroup G) :
    Continuous (fun p : G × LeftQuotient H => rightTranslate H p.1 p.2) := by
  have h := leftQuotient_isOpenQuotientMap H
  rw [← (IsOpenQuotientMap.id.prodMap h).continuous_comp_iff]
  change Continuous (fun p : G × G => leftQuotientMap H (p.2 * p.1))
  exact h.continuous.comp (continuous_snd.mul continuous_fst)

/-- Right translation of the quotient coordinate by the group coordinate. -/
def rightShear (H : Subgroup G) : G × LeftQuotient H ≃ₜ G × LeftQuotient H where
  toFun p := (p.1, rightTranslate H p.1 p.2)
  invFun p := (p.1, rightTranslate H p.1⁻¹ p.2)
  left_inv p := Prod.ext rfl (by simp [rightTranslate_mul])
  right_inv p := Prod.ext rfl (by simp [rightTranslate_mul])
  continuous_toFun := continuous_fst.prodMk (continuous_rightTranslate_joint H)
  continuous_invFun := continuous_fst.prodMk ((continuous_rightTranslate_joint H).comp
    (continuous_fst.inv.prodMk continuous_snd))

@[simp]
theorem rightShear_apply (H : Subgroup G) (g : G) (q : LeftQuotient H) :
    rightShear H (g, q) = (g, rightTranslate H g q) := rfl

@[simp]
theorem rightShear_apply_mk (H : Subgroup G) (g x : G) :
    rightShear H (g, leftQuotientMap H x) = (g, leftQuotientMap H (x * g)) := rfl

variable [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Right invariance of the quotient measure gives preservation of the product measure by
the shear. The group factor is arbitrary and s-finite. -/
def QuotientRightShearStatement : Prop :=
  ∀ (H : Subgroup G) [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μ : Measure G) (ν : Measure (LeftQuotient H)) [SFinite μ] [SFinite ν],
    (∀ g : G, MeasurePreserving (rightTranslate H g) ν ν) →
      MeasurePreserving (rightShear H) (μ.prod ν) (μ.prod ν)

theorem quotientRightShear_measurePreserving : QuotientRightShearStatement (G := G) := by
  intro H _ _ μ ν _ _ hr
  have : SecondCountableTopology (LeftQuotient H) :=
    (leftQuotient_isOpenQuotientMap H).secondCountableTopology
  exact (MeasurePreserving.id μ).skew_product (continuous_rightTranslate_joint H).measurable
    (ae_of_all _ fun g => (hr g).map_eq)

end Langlands.QuotientIntegration
