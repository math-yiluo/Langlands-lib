import Langlands.Analysis.Local.QuotientTopology
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Real compactly supported averaging on a left quotient

The averaging measure is right invariant because the cosets are `H * g`.
Compact support and continuity are proved from the subgroup embedding and
local uniform compact support, without countability assumptions.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology Pointwise CompactlySupported

universe u
variable {G : Type u} [Group G]

section Averaging

variable (H : Subgroup G) [MeasurableSpace H] [MeasurableMul H]
variable (μH : Measure H) [IsMulRightInvariant μH]

/-- The actual real Bochner integral along the left coset `H * g`. -/
def orbitAverageReal (f : G → ℝ) (g : G) : ℝ :=
  ∫ h : H, f (h.val * g) ∂μH

theorem orbitAverageReal_left_mul (f : G → ℝ) (h : H) (g : G) :
    orbitAverageReal H μH f (h.val * g) = orbitAverageReal H μH f g := by
  simpa only [orbitAverageReal, Subgroup.coe_mul, mul_assoc] using
    integral_mul_right_eq_self (μ := μH) (fun k : H => f (k.val * g)) h

/-- Real orbital averaging descended to the actual left quotient. -/
def quotientAverageReal (f : G → ℝ) : LeftQuotient H → ℝ :=
  descend H (orbitAverageReal H μH f) (orbitAverageReal_left_mul H μH f)

@[simp] theorem quotientAverageReal_mk (f : G → ℝ) (g : G) :
    quotientAverageReal H μH f (Quotient.mk _ g) = ∫ h : H, f (h.val * g) ∂μH := rfl

theorem quotientAverageReal_nonneg (f : G → ℝ) (hf : ∀ g, 0 ≤ f g)
    (q : LeftQuotient H) : 0 ≤ quotientAverageReal H μH f q := by
  induction q using Quotient.inductionOn with
  | h g => exact integral_nonneg (fun h => hf (h.val * g))

/-- Compatibility holds for the actual total Bochner integrals. -/
theorem quotientAverage_ofReal (f : G → ℝ) (q : LeftQuotient H) :
    quotientAverage H μH (fun g => (f g : ℂ)) q =
      (quotientAverageReal H μH f q : ℂ) := by
  induction q using Quotient.inductionOn with
  | h g => exact integral_complex_ofReal

theorem quotientAverageReal_rightTranslate [TopologicalSpace G] [IsTopologicalGroup G]
    (f : G → ℝ) (g : G) (q : LeftQuotient H) :
    quotientAverageReal H μH f (rightTranslate H g q) =
      quotientAverageReal H μH (fun x => f (x * g)) q := by
  induction q using Quotient.inductionOn with
  | h x => simp only [rightTranslate_mk, quotientAverageReal_mk, mul_assoc]

end Averaging

section Analytic

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [IsFiniteMeasureOnCompacts μH]

omit [MeasurableSpace H] [BorelSpace H] in
include hH in
/-- Compact support on a closed subgroup fiber, with arbitrary zero-valued codomain. -/
theorem hasCompactSupport_subgroup_mul_of_hasCompactSupport {E : Type*} [Zero E]
    (f : G → E) (hf : HasCompactSupport f) (g : G) :
    HasCompactSupport (fun h : H => f (h.val * g)) :=
  hf.comp_isClosedEmbedding
    ((Homeomorph.mulRight g).isClosedEmbedding.comp hH.isClosedEmbedding_subtypeVal)

include hH in
/-- Fiber integrability for any normed additive codomain, including real and complex scalars. -/
theorem integrable_subgroup_mul_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    (f : G → E) (hf : Continuous f) (hc : HasCompactSupport f) (g : G) :
    Integrable (fun h : H => f (h.val * g)) μH :=
  (hf.comp (continuous_subtype_val.mul_const g)).integrable_of_hasCompactSupport
    (hasCompactSupport_subgroup_mul_of_hasCompactSupport H hH f hc g)

omit [MeasurableSpace H] [BorelSpace H] in
include hH in
/-- A closed subgroup fiber meets compact support in a compact set. -/
theorem hasCompactSupport_subgroup_mul (f : C_c(G, ℝ)) (g : G) :
    HasCompactSupport (fun h : H => f (h.val * g)) := by
  exact hasCompactSupport_subgroup_mul_of_hasCompactSupport H hH f f.hasCompactSupport g

include hH in
/-- Every fiber is integrable with no global countability assumption. -/
theorem integrable_subgroup_mul (f : C_c(G, ℝ)) (g : G) :
    Integrable (fun h : H => f (h.val * g)) μH := by
  exact integrable_subgroup_mul_of_hasCompactSupport H hH μH f f.continuous f.hasCompactSupport g

variable [LocallyCompactSpace G]

include hH in
/-- Local uniform compact support gives continuity of the orbital integral. -/
theorem continuous_orbitAverageReal (f : C_c(G, ℝ)) :
    Continuous (orbitAverageReal H μH f) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, hUc, hUg⟩ := exists_compact_mem_nhds g
  let K : Set H := Subtype.val ⁻¹' (tsupport f * U⁻¹)
  have hK : IsCompact K :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage (f.hasCompactSupport.mul hUc.inv)
  have hc : ContinuousOn (fun p : G × H => f (p.2.val * p.1)) (U ×ˢ univ) :=
    (f.continuous.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).continuousOn
  have hz : ∀ p, ∀ h : H, p ∈ U → h ∉ K → f (h.val * p) = 0 := by
    intro p h hp hh
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hh
    change h.val ∈ tsupport f * U⁻¹
    exact ⟨h.val * p, hs, p⁻¹, by simpa, by simp⟩
  exact (continuousOn_integral_of_compact_support (μ := μH) hK hc hz).continuousAt hUg

variable [IsMulRightInvariant μH]

include hH in
/-- Continuity descends through the quotient topology. -/
theorem continuous_quotientAverageReal (f : C_c(G, ℝ)) :
    Continuous (quotientAverageReal H μH f) := by
  exact (continuous_orbitAverageReal H hH μH f).quotient_lift _

omit [IsFiniteMeasureOnCompacts μH] [LocallyCompactSpace G] in
/-- A nonzero average is supported over the original support. -/
theorem support_quotientAverageReal_subset (f : C_c(G, ℝ)) :
    Function.support (quotientAverageReal H μH f) ⊆
      (Quotient.mk (QuotientGroup.rightRel H)) '' tsupport f := by
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    by_contra hn
    apply hq
    change (∫ h : H, f (h.val * g) ∂μH) = 0
    have hz : ∀ h : H, f (h.val * g) = 0 := by
      intro h
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      apply hn
      refine ⟨h.val * g, hs, ?_⟩
      apply Quotient.sound
      apply QuotientGroup.rightRel_apply.mpr
      simp [mul_inv_rev]
    simp only [hz, integral_zero]

omit [IsFiniteMeasureOnCompacts μH] [LocallyCompactSpace G] in
include hH in
theorem hasCompactSupport_quotientAverageReal (f : C_c(G, ℝ)) :
    HasCompactSupport (quotientAverageReal H μH f) := by
  let := leftQuotient_t2Space H hH
  have hc : IsCompact ((Quotient.mk (QuotientGroup.rightRel H)) '' tsupport f) :=
    f.hasCompactSupport.image continuous_quotient_mk'
  exact hc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal
    (support_quotientAverageReal_subset H μH f) hc.isClosed)

include hH in
/-- The actual averaging operator as a positive real linear map. -/
def quotientAverageRealPositive : C_c(G, ℝ) →ₚ[ℝ] C_c(LeftQuotient H, ℝ) where
  toFun f :=
    { toFun := quotientAverageReal H μH f
      continuous_toFun := continuous_quotientAverageReal H hH μH f
      hasCompactSupport' := hasCompactSupport_quotientAverageReal H hH μH f }
  map_add' f k := by
    ext q
    induction q using Quotient.inductionOn with
    | h g =>
      exact integral_add (integrable_subgroup_mul H hH μH f g)
        (integrable_subgroup_mul H hH μH k g)
  map_smul' c f := by
    ext q
    induction q using Quotient.inductionOn with
    | h g => exact integral_smul c (fun h : H => f (h.val * g))
  monotone' := by
    intro f k hfk q
    induction q using Quotient.inductionOn with
    | h g =>
      exact integral_mono (integrable_subgroup_mul H hH μH f g)
        (integrable_subgroup_mul H hH μH k g) (fun h => hfk (h.val * g))

/-- The underlying real linear map. -/
def quotientAverageRealLinear : C_c(G, ℝ) →ₗ[ℝ] C_c(LeftQuotient H, ℝ) :=
  (quotientAverageRealPositive H hH μH).toLinearMap

@[simp] theorem quotientAverageRealPositive_apply (f : C_c(G, ℝ)) (q : LeftQuotient H) :
    quotientAverageRealPositive H hH μH f q = quotientAverageReal H μH f q := rfl

@[simp] theorem quotientAverageRealLinear_apply (f : C_c(G, ℝ)) (q : LeftQuotient H) :
    quotientAverageRealLinear H hH μH f q = quotientAverageReal H μH f q := rfl

@[simp] theorem quotientAverageRealLinear_mk (f : C_c(G, ℝ)) (g : G) :
    quotientAverageRealLinear H hH μH f (Quotient.mk _ g) =
      ∫ h : H, f (h.val * g) ∂μH := rfl

theorem quotientAverageRealLinear_nonneg (f : C_c(G, ℝ)) (hf : 0 ≤ f) :
    0 ≤ quotientAverageRealLinear H hH μH f :=
  (quotientAverageRealPositive H hH μH).map_nonneg hf

end Analytic

end Langlands.QuotientIntegration
