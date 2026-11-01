import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! Compatible quotient measures transported through actual group equivalences. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure

universe uG uK

variable {G : Type uG} {G' : Type uK} [Group G] [Group G']
  [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace G'] [IsTopologicalGroup G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

/-- Restrict a continuous group equivalence to corresponding actual subgroups. -/
def subgroupContinuousMulEquiv (e : G ≃ₜ* G') (H : Subgroup G) (K : Subgroup G')
    (h : ∀ x : G, e x ∈ K ↔ x ∈ H) : H ≃ₜ* K where
  toFun x := ⟨e x, (h x).2 x.property⟩
  invFun y := ⟨e.symm y, (h (e.symm y)).1 (by rw [e.apply_symm_apply]; exact y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Right Haar invariance is preserved by pushforward along a continuous group
isomorphism, with no scalar renormalization. -/
theorem isMulRightInvariant_map (e : G ≃ₜ* G') (μ : Measure G)
    [IsMulRightInvariant μ] : IsMulRightInvariant (Measure.map e μ) where
  map_mul_right_eq_self g := by
    have he : Measurable (e : G → G') := e.continuous.measurable
    rw [Measure.map_map (measurable_mul_const g) he]
    have h : (fun x : G => e x * g) = e ∘ (fun x => x * e.symm g) := by
      funext x
      simp only [Function.comp_apply, map_mul, e.apply_symm_apply]
    rw [show (fun x : G' => x * g) ∘ e = (fun x : G => e x * g) from rfl,
      h, ← Measure.map_map he (measurable_mul_const _),
      map_mul_right_eq_self]

variable (e : G ≃ₜ* G') (H : Subgroup G) (K : Subgroup G')
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace K] [BorelSpace K]
  (eH : H ≃ₜ* K) (heH : ∀ h : H, (eH h : G') = e h)
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [MeasurableSpace (LeftQuotient K)] [BorelSpace (LeftQuotient K)]
  (eQ : LeftQuotient H ≃ₜ LeftQuotient K)
  (heQ : ∀ x : G, eQ (Quotient.mk _ x) = Quotient.mk _ (e x))
  (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]

local instance : IsMulRightInvariant (Measure.map eH μH) :=
  isMulRightInvariant_map eH μH

include heH heQ

/-- The actual subgroup averages agree after simultaneous group, subgroup and
quotient pushforward. -/
theorem quotientAverage_map_equiv (f : G' → ℂ) (q : LeftQuotient H) :
    quotientAverage K (Measure.map eH μH) f (eQ q) =
      quotientAverage H μH (f ∘ e) q := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [heQ, quotientAverage_mk, quotientAverage_mk]
    calc
      (∫ h : K, f (h.val * e x) ∂Measure.map eH μH) =
          ∫ h : H, f ((eH h : G') * e x) ∂μH :=
        integral_map_equiv eH.toHomeomorph.toMeasurableEquiv _
      _ = _ := by
        congr 1
        funext h
        simp only [Function.comp_apply, map_mul, heH]

/-- All fields of the Weil compatibility property are preserved by the same
three pushforwards. -/
theorem isCompatible_map_equiv (ν : Measure (LeftQuotient H))
    (hc : IsCompatible H μG μH ν) :
    IsCompatible K (Measure.map e μG) (Measure.map eH μH) (Measure.map eQ ν) where
  nonzero := (Measure.map_ne_zero_iff eQ.continuous.measurable.aemeasurable).2 hc.nonzero
  regular := by
    let := hc.regular
    exact Measure.Regular.map eQ
  right_invariant g := by
    refine ⟨(rightTranslate K g).continuous.measurable, ?_⟩
    have hcomm : (rightTranslate K g) ∘ eQ =
        eQ ∘ (rightTranslate H (e.symm g)) := by
      funext q
      induction q using Quotient.inductionOn with
      | h x => simp only [Function.comp_apply, heQ, rightTranslate_mk, map_mul,
          e.apply_symm_apply]
    rw [Measure.map_map (rightTranslate K g).continuous.measurable eQ.continuous.measurable,
      hcomm, ← Measure.map_map eQ.continuous.measurable
        (rightTranslate H (e.symm g)).continuous.measurable,
      (hc.right_invariant (e.symm g)).map_eq]
  averaging_integrable f hf hfc := by
    apply (integrable_map_equiv eQ.toMeasurableEquiv _).2
    change Integrable (fun q => quotientAverage K (Measure.map eH μH) f (eQ q)) ν
    simp_rw [quotientAverage_map_equiv e H K eH heH eQ heQ μH]
    exact hc.averaging_integrable (f ∘ e) (hf.comp e.continuous)
      (hfc.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding)
  integral_formula f hf hfc := by
    calc
      (∫ q, quotientAverage K (Measure.map eH μH) f q ∂Measure.map eQ ν) =
          ∫ q, quotientAverage K (Measure.map eH μH) f (eQ q) ∂ν :=
        integral_map_equiv eQ.toMeasurableEquiv _
      _ = ∫ q, quotientAverage H μH (f ∘ e) q ∂ν := by
        congr 1
        funext q
        exact quotientAverage_map_equiv e H K eH heH eQ heQ μH f q
      _ = ∫ x, (f ∘ e) x ∂μG :=
        hc.integral_formula (f ∘ e) (hf.comp e.continuous)
          (hfc.comp_isClosedEmbedding e.toHomeomorph.isClosedEmbedding)
      _ = ∫ x, f x ∂Measure.map e μG :=
        (integral_map_equiv e.toHomeomorph.toMeasurableEquiv f).symm

end Langlands.QuotientIntegration
