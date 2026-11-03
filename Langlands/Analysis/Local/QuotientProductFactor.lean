import Langlands.Analysis.Local.QuotientMeasureEquiv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Removing a full direct factor from a compatible quotient measure -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped Topology CompactlySupported

universe uA uN

section Quotient

variable (A : Type uA) {N : Type uN} [Group A] [Group N]
variable [TopologicalSpace A] [IsTopologicalGroup A]
variable [TopologicalSpace N] [IsTopologicalGroup N]
variable (H : Subgroup N)

/-- The actual subgroup containing the whole first direct factor. -/
abbrev fullFactorSubgroup : Subgroup (A × N) := (⊤ : Subgroup A).prod H

/-- Restrict the second factor while retaining the whole first factor. -/
def fullFactorSubgroupEquiv : A × H ≃ₜ* fullFactorSubgroup A H := by
  exact {
    toFun p := ⟨(p.1, p.2.val), ⟨Subgroup.mem_top _, p.2.property⟩⟩
    invFun p := (p.val.1, ⟨p.val.2, p.property.2⟩)
    left_inv p := rfl
    right_inv p := Subtype.ext rfl
    map_mul' p q := Subtype.ext rfl
    continuous_toFun := (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk
        (fun p => p.property.2)) }

omit [IsTopologicalGroup A] [IsTopologicalGroup N] in
@[simp] theorem fullFactorSubgroupEquiv_apply (p : A × H) :
    (fullFactorSubgroupEquiv A H p : A × N) = (p.1, p.2.val) := rfl

/-- The quotient by the full first factor and `H` is exactly the second quotient. -/
def fullFactorQuotientEquiv : LeftQuotient (fullFactorSubgroup A H) ≃ₜ
    LeftQuotient H where
  toFun := Quotient.map Prod.snd (by
    intro x y h
    exact QuotientGroup.rightRel_apply.mpr (QuotientGroup.rightRel_apply.mp h).2)
  invFun := Quotient.map (fun n : N => ((1 : A), n)) (by
    intro x y h
    exact QuotientGroup.rightRel_apply.mpr
      ⟨Subgroup.mem_top _, QuotientGroup.rightRel_apply.mp h⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      exact ⟨Subgroup.mem_top _, by simp⟩
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h n => rfl
  continuous_toFun :=
    (continuous_quotient_mk'.comp continuous_snd).quotient_lift _
  continuous_invFun :=
    (continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)).quotient_lift _

omit [IsTopologicalGroup A] [IsTopologicalGroup N] in
@[simp] theorem fullFactorQuotientEquiv_mk (p : A × N) :
    fullFactorQuotientEquiv A H (Quotient.mk _ p) = Quotient.mk _ p.2 := rfl

omit [IsTopologicalGroup A] [IsTopologicalGroup N] in
@[simp] theorem fullFactorQuotientEquiv_symm_mk (n : N) :
    (fullFactorQuotientEquiv A H).symm (Quotient.mk _ n) =
      Quotient.mk _ ((1 : A), n) := rfl

theorem fullFactorQuotientEquiv_rightTranslate (g : A × N)
    (q : LeftQuotient (fullFactorSubgroup A H)) :
    fullFactorQuotientEquiv A H (rightTranslate (fullFactorSubgroup A H) g q) =
      rightTranslate H g.2 (fullFactorQuotientEquiv A H q) := by
  induction q using Quotient.inductionOn with
  | h p => rfl

end Quotient

section PartialIntegral

variable (A : Type uA) {N : Type uN} [TopologicalSpace A] [TopologicalSpace N]
variable [MeasurableSpace A] [BorelSpace A] [T2Space N]
variable (μA : Measure A) [IsFiniteMeasureOnCompacts μA]

omit [T2Space N] in
/-- Compact support in the product gives uniform compact support for integration
over the first factor, hence a continuous function of the second factor. -/
theorem continuous_integral_fullFactor (f : C_c(A × N, ℂ)) :
    Continuous (fun n : N => ∫ a : A, f (a, n) ∂μA) := by
  have hk : IsCompact (Prod.fst '' tsupport f) :=
    f.hasCompactSupport.image continuous_fst
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (μ := μA)
    (f := fun n a => f (a, n)) hk
    (f.continuous.comp continuous_swap).continuousOn
  intro n a _ ha
  apply image_eq_zero_of_notMem_tsupport
  exact fun h => ha ⟨(a, n), h, rfl⟩

omit [BorelSpace A] [IsFiniteMeasureOnCompacts μA] in
/-- The support of the partial integral stays in the compact second projection. -/
theorem hasCompactSupport_integral_fullFactor (f : C_c(A × N, ℂ)) :
    HasCompactSupport (fun n : N => ∫ a : A, f (a, n) ∂μA) := by
  have hk : IsCompact (Prod.snd '' tsupport f) :=
    f.hasCompactSupport.image continuous_snd
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hk.isClosed
  intro n hn
  by_contra h
  apply hn
  have hz : ∀ a : A, f (a, n) = 0 := by
    intro a
    apply image_eq_zero_of_notMem_tsupport
    exact fun hp => h ⟨(a, n), hp, rfl⟩
  simp only [hz, integral_zero]

/-- Integrating out the full factor retains actual continuous compact tests. -/
def compactIntegralFullFactor (f : C_c(A × N, ℂ)) : C_c(N, ℂ) where
  toFun n := ∫ a : A, f (a, n) ∂μA
  continuous_toFun := continuous_integral_fullFactor A μA f
  hasCompactSupport' := hasCompactSupport_integral_fullFactor A μA f

@[simp] theorem compactIntegralFullFactor_apply (f : C_c(A × N, ℂ)) (n : N) :
    compactIntegralFullFactor A μA f n = ∫ a : A, f (a, n) ∂μA := rfl

end PartialIntegral

section Measures

variable (A : Type uA) {N : Type uN} [Group A] [Group N]
variable [TopologicalSpace A] [IsTopologicalGroup A]
variable [TopologicalSpace N] [IsTopologicalGroup N] [T2Space N]
variable [SecondCountableTopology A] [SecondCountableTopology N]
variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace N] [BorelSpace N]
variable (H : Subgroup N) [MeasurableSpace H] [BorelSpace H]
variable (μA : Measure A) (μH : Measure H)

/-- Exact product normalization on the actual full-factor subgroup. -/
def fullFactorSubgroupMeasure : Measure (fullFactorSubgroup A H) :=
  Measure.map (fullFactorSubgroupEquiv A H) (μA.prod μH)

variable [IsMulRightInvariant μA] [IsMulRightInvariant μH]
variable [SigmaFinite μA] [SigmaFinite μH]

/-- Both factor measures retain their normalization under subgroup transport. -/
instance fullFactorSubgroupMeasure_rightInvariant :
    IsMulRightInvariant (fullFactorSubgroupMeasure A H μA μH) :=
  isMulRightInvariant_map (fullFactorSubgroupEquiv A H) (μA.prod μH)

variable [IsFiniteMeasureOnCompacts μA] [IsFiniteMeasureOnCompacts μH]

/-- Fubini and right invariance integrate out precisely the full first factor. -/
theorem quotientAverage_fullFactor (hH : IsClosed (H : Set N))
    (f : C_c(A × N, ℂ)) (q : LeftQuotient (fullFactorSubgroup A H)) :
    quotientAverage (fullFactorSubgroup A H) (fullFactorSubgroupMeasure A H μA μH) f q =
      quotientAverage H μH (compactIntegralFullFactor A μA f)
        (fullFactorQuotientEquiv A H q) := by
  induction q using Quotient.inductionOn with
  | h p =>
    rw [fullFactorQuotientEquiv_mk, quotientAverage_mk, quotientAverage_mk]
    have hj : Topology.IsClosedEmbedding
        (fun ah : A × H => (ah.1, ah.2.val) * p) :=
      (Homeomorph.mulRight p).isClosedEmbedding.comp
        (Topology.IsClosedEmbedding.id.prodMap hH.isClosedEmbedding_subtypeVal)
    have hfiber : Integrable (fun ah : A × H => f ((ah.1, ah.2.val) * p))
        (μA.prod μH) :=
      (f.continuous.comp hj.continuous).integrable_of_hasCompactSupport
        (f.hasCompactSupport.comp_isClosedEmbedding hj)
    calc
      (∫ k : fullFactorSubgroup A H, f (k.val * p)
          ∂fullFactorSubgroupMeasure A H μA μH) =
          ∫ ah : A × H, f ((ah.1, ah.2.val) * p) ∂μA.prod μH :=
        integral_map_equiv (fullFactorSubgroupEquiv A H).toHomeomorph.toMeasurableEquiv _
      _ = ∫ h : H, ∫ a : A, f (a * p.1, h.val * p.2) ∂μA ∂μH :=
        integral_prod_symm _ hfiber
      _ = ∫ h : H, compactIntegralFullFactor A μA f (h.val * p.2) ∂μH := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun h =>
          integral_mul_right_eq_self (μ := μA) (fun a => f (a, h.val * p.2)) p.1)

variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable [MeasurableSpace (LeftQuotient (fullFactorSubgroup A H))]
variable [BorelSpace (LeftQuotient (fullFactorSubgroup A H))]

/-- The supplied second quotient measure on the actual product quotient. -/
def fullFactorQuotientMeasure (ν : Measure (LeftQuotient H)) :
    Measure (LeftQuotient (fullFactorSubgroup A H)) :=
  Measure.map (fullFactorQuotientEquiv A H).symm ν

/-- Compatibility with a supplied second quotient gives every compatibility
field on the product quotient, with exact product and pushforward measures. -/
theorem fullFactorQuotientMeasure_isCompatible (hH : IsClosed (H : Set N))
    (μN : Measure N) [IsFiniteMeasureOnCompacts μN] [SigmaFinite μN]
    (ν : Measure (LeftQuotient H)) (hc : IsCompatible H μN μH ν) :
    IsCompatible (fullFactorSubgroup A H) (μA.prod μN)
      (fullFactorSubgroupMeasure A H μA μH) (fullFactorQuotientMeasure A H ν) where
  nonzero := (Measure.map_ne_zero_iff
    (fullFactorQuotientEquiv A H).symm.continuous.measurable.aemeasurable).2 hc.nonzero
  regular := by
    let := hc.regular
    exact Measure.Regular.map (fullFactorQuotientEquiv A H).symm
  right_invariant p := by
    refine ⟨(rightTranslate _ p).continuous.measurable, ?_⟩
    have hcomm : rightTranslate (fullFactorSubgroup A H) p ∘
        (fullFactorQuotientEquiv A H).symm =
        (fullFactorQuotientEquiv A H).symm ∘ rightTranslate H p.2 := by
      funext q
      apply (fullFactorQuotientEquiv A H).injective
      simp only [Function.comp_apply, fullFactorQuotientEquiv_rightTranslate,
        Homeomorph.apply_symm_apply]
    rw [fullFactorQuotientMeasure,
      Measure.map_map (rightTranslate _ p).continuous.measurable
        (fullFactorQuotientEquiv A H).symm.continuous.measurable,
      hcomm, ← Measure.map_map
        (fullFactorQuotientEquiv A H).symm.continuous.measurable
        (rightTranslate H p.2).continuous.measurable,
      (hc.right_invariant p.2).map_eq]
  averaging_integrable f hf hfc := by
    let F : C_c(A × N, ℂ) := ⟨⟨f, hf⟩, hfc⟩
    apply (integrable_map_equiv (fullFactorQuotientEquiv A H).symm.toMeasurableEquiv _).2
    change Integrable (fun q =>
      quotientAverage (fullFactorSubgroup A H) (fullFactorSubgroupMeasure A H μA μH)
        F ((fullFactorQuotientEquiv A H).symm q)) ν
    simp_rw [quotientAverage_fullFactor A H μA μH hH,
      Homeomorph.apply_symm_apply]
    exact hc.averaging_integrable _ (compactIntegralFullFactor A μA F).continuous
      (compactIntegralFullFactor A μA F).hasCompactSupport
  integral_formula f hf hfc := by
    let F : C_c(A × N, ℂ) := ⟨⟨f, hf⟩, hfc⟩
    have hF : Integrable F (μA.prod μN) :=
      F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport
    calc
      (∫ q, quotientAverage (fullFactorSubgroup A H)
          (fullFactorSubgroupMeasure A H μA μH) f q
          ∂fullFactorQuotientMeasure A H ν) =
          ∫ q, quotientAverage (fullFactorSubgroup A H)
            (fullFactorSubgroupMeasure A H μA μH) F
            ((fullFactorQuotientEquiv A H).symm q) ∂ν :=
        integral_map_equiv (fullFactorQuotientEquiv A H).symm.toMeasurableEquiv _
      _ = ∫ q, quotientAverage H μH (compactIntegralFullFactor A μA F) q ∂ν := by
        simp_rw [quotientAverage_fullFactor A H μA μH hH,
          Homeomorph.apply_symm_apply]
      _ = ∫ n, compactIntegralFullFactor A μA F n ∂μN :=
        hc.integral_formula _ (compactIntegralFullFactor A μA F).continuous
          (compactIntegralFullFactor A μA F).hasCompactSupport
      _ = ∫ p, f p ∂μA.prod μN := (integral_prod_symm F hF).symm

end Measures

end Langlands.QuotientIntegration
