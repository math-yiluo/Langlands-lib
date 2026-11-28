import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Langlands.Representation.Hecke.CentralCharacterTest
import Langlands.Topology.LocallyConstant.QuotientDescent

/-! # Convolution of tests with a fixed central character -/

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Set Topology
open scoped Pointwise

namespace Langlands.Hecke.CentralCharacterTest

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {Z : Subgroup G} [Z.Normal] {ω : SmoothUnitaryCharacter Z}
variable (hcentral : Z ≤ Subgroup.center G)

section Integrand

variable (f₁ f₂ : CentralCharacterTest Z ω)

include hcentral in
private theorem convolutionKernel_left_mul (g : G) (z : Z) (x : G) :
    f₁ (z.val * x) * f₂ ((z.val * x)⁻¹ * g) = f₁ x * f₂ (x⁻¹ * g) := by
  have hcomm : x⁻¹ * (z⁻¹ : Z).val = (z⁻¹ : Z).val * x⁻¹ :=
    Subgroup.mem_center_iff.mp (hcentral (z⁻¹ : Z).property) x⁻¹
  have he : (z.val * x)⁻¹ * g = (z⁻¹ : Z).val * (x⁻¹ * g) := by
    rw [mul_inv_rev]
    change x⁻¹ * (z⁻¹ : Z).val * g = _
    rw [hcomm, mul_assoc]
  rw [he, f₁.equivariant, f₂.equivariant, ω.complex_inv, inv_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ (Circle.coe_ne_zero (ω z)), one_mul]

/-- The kernel `x ↦ f₁(x) f₂(x⁻¹ g)` descended to the quotient of `G` by `Z`. -/
def convolutionIntegrand (g : G) (x : G ⧸ Z) : ℂ :=
  QuotientIntegration.descend Z (fun y => f₁ y * f₂ (y⁻¹ * g))
    (convolutionKernel_left_mul hcentral f₁ f₂ g)
    ((QuotientIntegration.normalLeftQuotientHomeomorph Z).symm x)

@[simp] theorem convolutionIntegrand_mk (g x : G) :
    convolutionIntegrand hcentral f₁ f₂ g (QuotientGroup.mk x) =
      f₁ x * f₂ (x⁻¹ * g) := by
  rw [← QuotientIntegration.normalLeftQuotientHomeomorph_mk Z x, convolutionIntegrand,
    Homeomorph.symm_apply_apply, QuotientIntegration.descend_mk]

theorem support_convolutionIntegrand_subset (g : G) :
    support (convolutionIntegrand hcentral f₁ f₂ g) ⊆ quotientSupport Z f₁ := by
  intro q hq
  obtain ⟨x, rfl⟩ := (QuotientGroup.isQuotientMap_mk Z).surjective q
  rw [mem_support, convolutionIntegrand_mk] at hq
  exact ⟨x, (mul_ne_zero_iff.mp hq).1, rfl⟩

variable [IsTopologicalGroup G]

/-- The descended kernel is locally constant jointly in the output point and the coset. -/
theorem convolutionIntegrand_jointlyLocallyConstant :
    IsLocallyConstant
      (fun p : G × (G ⧸ Z) => convolutionIntegrand hcentral f₁ f₂ p.1 p.2) := by
  let p : G × G → G × (G ⧸ Z) := Prod.map id QuotientGroup.mk
  have hp : IsQuotientMap p :=
    (IsOpenQuotientMap.id.prodMap QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
  apply (LocallyConstantQuotient.isLocallyConstant_iff p hp _).2
  have h₁ := f₁.locallyConstant.comp_continuous (continuous_snd : Continuous (Prod.snd : G × G → G))
  have h₂ := f₂.locallyConstant.comp_continuous
    (continuous_snd.inv.mul continuous_fst : Continuous (fun x : G × G => x.2⁻¹ * x.1))
  have hmul : IsLocallyConstant (fun x : G × G => f₁ x.2 * f₂ (x.2⁻¹ * x.1)) := h₁.mul h₂
  simpa [p, Function.comp_def] using hmul

end Integrand

section Integral

variable [IsTopologicalGroup G] [MeasurableSpace (G ⧸ Z)]
variable (μ : Measure (G ⧸ Z)) (f₁ f₂ : CentralCharacterTest Z ω)

/-- The descended kernel is integrable for a Borel measure finite on compact sets. -/
theorem convolutionIntegrand_integrable [BorelSpace (G ⧸ Z)] [IsFiniteMeasureOnCompacts μ]
    (g : G) : Integrable (convolutionIntegrand hcentral f₁ f₂ g) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact ((convolutionIntegrand_jointlyLocallyConstant hcentral f₁ f₂).comp_continuous
      (continuous_const.prodMk continuous_id : Continuous (fun q : G ⧸ Z => (g, q)))).continuous
  · exact HasCompactSupport.of_support_subset_isCompact f₁.isCompact_quotientSupport
      (support_convolutionIntegrand_subset hcentral f₁ f₂ g)

private def convolutionValue (g : G) : ℂ :=
  ∫ x, convolutionIntegrand hcentral f₁ f₂ g x ∂μ

private theorem convolutionValue_locallyConstant :
    IsLocallyConstant (convolutionValue hcentral μ f₁ f₂) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro g
  have hloc := convolutionIntegrand_jointlyLocallyConstant hcentral f₁ f₂
  have hfixed : IsLocallyConstant
      (fun p : G × (G ⧸ Z) => convolutionIntegrand hcentral f₁ f₂ g p.2) :=
    hloc.comp_continuous (continuous_const.prodMk continuous_snd)
  have he : ∀ᶠ y in 𝓝 g, ∀ q ∈ quotientSupport Z f₁,
      convolutionIntegrand hcentral f₁ f₂ y q = convolutionIntegrand hcentral f₁ f₂ g q := by
    apply f₁.isCompact_quotientSupport.eventually_forall_of_forall_eventually
    intro q _
    filter_upwards [hloc.eventually_eq (g, q), hfixed.eventually_eq (g, q)] with p hp hq
    exact hp.trans hq.symm
  filter_upwards [he] with y hy
  apply integral_congr_ae (Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ quotientSupport Z f₁
  · exact hy q hq
  · have hz (x : G) : convolutionIntegrand hcentral f₁ f₂ x q = 0 :=
      not_ne_iff.mp (fun hn => hq (support_convolutionIntegrand_subset hcentral f₁ f₂ x hn))
    rw [hz y, hz g]

omit [IsTopologicalGroup G] in
private theorem convolutionValue_equivariant (z : Z) (g : G) :
    convolutionValue hcentral μ f₁ f₂ (z.val * g) =
      (ω z : ℂ)⁻¹ * convolutionValue hcentral μ f₁ f₂ g := by
  unfold convolutionValue
  rw [← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun q => ?_)
  obtain ⟨x, rfl⟩ := (QuotientGroup.isQuotientMap_mk Z).surjective q
  simp only [convolutionIntegrand_mk]
  rw [← mul_assoc x⁻¹ z.val g, Subgroup.mem_center_iff.mp (hcentral z.property) x⁻¹,
    mul_assoc, f₂.equivariant, mul_left_comm (f₁ x)]

omit [IsTopologicalGroup G] in
private theorem quotientSupport_convolutionValue_subset :
    quotientSupport Z (convolutionValue hcentral μ f₁ f₂) ⊆
      quotientSupport Z f₁ * quotientSupport Z f₂ := by
  classical
  rintro _ ⟨g, hg, rfl⟩
  by_contra h
  apply hg
  apply integral_eq_zero_of_ae (Eventually.of_forall fun q => ?_)
  obtain ⟨x, rfl⟩ := (QuotientGroup.isQuotientMap_mk Z).surjective q
  change convolutionIntegrand hcentral f₁ f₂ g (QuotientGroup.mk x) = 0
  rw [convolutionIntegrand_mk]
  by_contra hne
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hne
  refine h ⟨QuotientGroup.mk x, ⟨x, h₁, rfl⟩, QuotientGroup.mk (x⁻¹ * g),
    ⟨x⁻¹ * g, h₂, rfl⟩, ?_⟩
  change (QuotientGroup.mk x : G ⧸ Z) * QuotientGroup.mk (x⁻¹ * g) = QuotientGroup.mk g
  rw [← QuotientGroup.mk_mul, mul_inv_cancel_left]

/-- Convolution of two central-character tests using the supplied quotient Haar measure. -/
def convolution [BorelSpace (G ⧸ Z)] [μ.IsHaarMeasure] : CentralCharacterTest Z ω := by
  have hl := convolutionValue_locallyConstant hcentral μ f₁ f₂
  have he := convolutionValue_equivariant hcentral μ f₁ f₂
  refine ⟨convolutionValue hcentral μ f₁ f₂, hl, ?_, he⟩
  exact (f₁.isCompact_quotientSupport.mul f₂.isCompact_quotientSupport).of_isClosed_subset
    (isClopen_quotientSupport_of_equivariant hl he).isClosed
    (quotientSupport_convolutionValue_subset hcentral μ f₁ f₂)

variable [BorelSpace (G ⧸ Z)] [μ.IsHaarMeasure]

@[simp] theorem convolution_apply (g : G) :
    convolution hcentral μ f₁ f₂ g = ∫ x, convolutionIntegrand hcentral f₁ f₂ g x ∂μ := rfl

theorem quotientSupport_convolution_subset :
    quotientSupport Z (convolution hcentral μ f₁ f₂) ⊆
      quotientSupport Z f₁ * quotientSupport Z f₂ :=
  quotientSupport_convolutionValue_subset hcentral μ f₁ f₂

end Integral

end Langlands.Hecke.CentralCharacterTest
