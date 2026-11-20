import Langlands.Global.RankinSelberg.UnfoldingMeasure
import Langlands.Global.LeftCosetHaarMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Unfolding along nested discrete subgroups, and Haar measure under automorphisms

Abstract measure theory for the constant-term computation of Bernstein–Lapid §6.10:

* `lintegral_out_eq`: the lower integral of a left-invariant function over a quotient measure
  built from a set of representatives is its lower integral over that set;
* `lintegral_unfold`, `integral_unfold`: for discrete `Λ ≤ Γ`, representatives `ρ` of `Λ \ Γ`
  and a strict fundamental domain `t` of `Γ`, the integral over `Λ \ H` (for the quotient measure
  built on the fundamental domain `⋃ ρ_i t` of `Λ`) of a left `Λ`-invariant function `f` equals
  the integral over `t` of `∑_i f(ρ_i v)`;
* `map_eq_self_of_preserves`: a continuous automorphism of a locally compact second-countable
  group which preserves a discrete subgroup `Γ` with a fundamental domain of finite positive
  Haar measure preserves Haar measure. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.EisensteinConstantTerm

open MeasureTheory Set Langlands.Global
open scoped ENNReal Pointwise

section Representatives

variable {H : Type*} [Group H] [MeasurableSpace H]

/-- The lower integral of a left `Γ`-invariant function, evaluated at quotient representatives,
for a quotient measure built from a set of representatives. -/
theorem lintegral_out_eq (Γ : Subgroup H) {f : H → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) (ν : Measure H) (s : Set H) :
    ∫⁻ q, f q.out ∂(LeftCosetSpace.quotientMeasure Γ ν s) = ∫⁻ x in s, f x ∂ν := by
  have hm : Measurable (LeftCosetSpace.lift Γ f hf) := measurable_from_quotient.mpr hfm
  rw [RankinSelbergGlobal.Unfolding.out_eq_lift Γ f hf, LeftCosetSpace.quotientMeasure,
    lintegral_map hm (LeftCosetSpace.measurable_mk Γ)]
  rfl

end Representatives

section Unfolding

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

/-- The translates `ρ_i t` of a strict fundamental domain `t` of `Γ` by representatives of
`Λ \ Γ` form a fundamental domain of `Λ`. -/
theorem isFundamentalDomain_iUnion_smul {Λ Γ : Subgroup H} (hΛΓ : Λ ≤ Γ)
    {t : Set H} (htm : MeasurableSet t) (ht : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ t)
    {ι : Type*} [Countable ι] (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ) (μ : Measure H) :
    IsFundamentalDomain Λ (⋃ i, ρ i • t) μ :=
  IsFundamentalDomain.mk' (MeasurableSet.iUnion fun i => htm.const_smul (ρ i)).nullMeasurableSet
    (RankinSelbergGlobal.Unfolding.existsUnique_mem_iUnion_smul hΛΓ ht ρ hρΓ hρ)

variable (μ : Measure H) [μ.IsMulLeftInvariant]

/-- Lower-integral unfolding: integrating `‖f‖` over `Λ \ H` is integrating the orbit sum of
`‖f‖` over a fundamental domain of `Γ`. -/
theorem lintegral_unfold {Λ Γ : Subgroup H}
    {t : Set H} (htm : MeasurableSet t) (ht : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ t)
    {ι : Type*} [Countable ι] (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ) {f : H → ℂ} (hfm : Measurable f)
    (hf : ∀ (l : Λ) (x : H), f ((l : H) * x) = f x) :
    ∫⁻ x, ‖f x.out‖ₑ ∂(LeftCosetSpace.quotientMeasure Λ μ (⋃ i, ρ i • t)) =
      ∫⁻ v in t, ∑' i, ‖f (ρ i * v)‖ₑ ∂μ := by
  rw [lintegral_out_eq Λ hfm.enorm (fun l x => by rw [hf l x]) μ _]
  have hdisj := RankinSelbergGlobal.Unfolding.pairwise_disjoint_smul (Λ := Λ) ht ρ hρΓ hρ
  have hmeas : ∀ i, MeasurableSet (ρ i • t) := fun i => htm.const_smul (ρ i)
  have hmp : ∀ i, MeasurePreserving (fun x => ρ i * x) μ μ := fun i =>
    measurePreserving_mul_left μ (ρ i)
  have hemb : ∀ i, MeasurableEmbedding (fun x : H => ρ i * x) := fun i =>
    measurableEmbedding_mulLeft (ρ i)
  have hpre : ∀ i, (fun x : H => ρ i * x) ⁻¹' (ρ i • t) = t := fun i => by
    ext x
    simp [mem_smul_set_iff_inv_smul_mem]
  have hlint : ∀ i, ∫⁻ x in ρ i • t, ‖f x‖ₑ ∂μ = ∫⁻ v in t, ‖f (ρ i * v)‖ₑ ∂μ := fun i => by
    conv_rhs => rw [← hpre i]
    exact ((hmp i).setLIntegral_comp_preimage_emb (hemb i) (fun x => ‖f x‖ₑ) (ρ i • t)).symm
  have hsum : ∫⁻ v in t, ∑' i, ‖f (ρ i * v)‖ₑ ∂μ = ∑' i, ∫⁻ v in t, ‖f (ρ i * v)‖ₑ ∂μ :=
    lintegral_tsum fun i => ((hfm.comp (measurable_const_mul (ρ i))).enorm).aemeasurable
  rw [lintegral_iUnion hmeas hdisj, hsum]
  exact tsum_congr hlint

/-- Integral unfolding, under finiteness of the unfolded lower integral of `‖f‖`. -/
theorem integral_unfold {Λ Γ : Subgroup H}
    {t : Set H} (htm : MeasurableSet t) (ht : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ t)
    {ι : Type*} [Countable ι] (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ) {f : H → ℂ} (hfm : Measurable f)
    (hf : ∀ (l : Λ) (x : H), f ((l : H) * x) = f x)
    (hfin : ∫⁻ v in t, ∑' i, ‖f (ρ i * v)‖ₑ ∂μ ≠ ∞) :
    Integrable (fun x => f x.out) (LeftCosetSpace.quotientMeasure Λ μ (⋃ i, ρ i • t)) ∧
      IntegrableOn (fun v => ∑' i, f (ρ i * v)) t μ ∧
      ∫ x, f x.out ∂(LeftCosetSpace.quotientMeasure Λ μ (⋃ i, ρ i • t)) =
        ∫ v in t, ∑' i, f (ρ i * v) ∂μ := by
  have hU : ∫⁻ x in ⋃ i, ρ i • t, ‖f x‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_out_eq Λ hfm.enorm (fun l x => by rw [hf l x]) μ _,
      lintegral_unfold μ htm ht ρ hρΓ hρ hfm hf]
    exact hfin
  have hfU : IntegrableOn f (⋃ i, ρ i • t) μ :=
    ⟨hfm.aestronglyMeasurable, hU.lt_top⟩
  obtain ⟨hint, heq⟩ :=
    RankinSelbergGlobal.Unfolding.integrableOn_tsum_and_setIntegral_eq μ htm ht ρ hρΓ hρ hfU
  refine ⟨(RankinSelbergGlobal.Unfolding.integrable_out_iff Λ hfm hf μ _).mpr hfU, hint, ?_⟩
  rw [RankinSelbergGlobal.Unfolding.integral_out_eq Λ hfm hf μ _, heq]

end Unfolding

section Automorphism

variable {H : Type*} [Group H]

/-- The preimage of a strict fundamental domain of `Γ` under an automorphism preserving `Γ` is
a strict fundamental domain of `Γ`. -/
theorem existsUnique_mem_preimage (Γ : Subgroup H) {s : Set H}
    (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s) (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (x : H) :
    ∃! γ : Γ, (γ : H) * x ∈ α ⁻¹' s := by
  obtain ⟨δ, hδ, huniq⟩ := hs (α x)
  have hmem : α.symm δ ∈ Γ := (hα _).mp (by simp)
  refine ⟨⟨α.symm δ, hmem⟩, ?_, ?_⟩
  · change α (α.symm δ * x) ∈ s
    simpa [map_mul] using hδ
  · intro γ hγ
    have hγ' : ((⟨α γ, (hα γ).mpr γ.2⟩ : Γ) : H) * α x ∈ s := by
      change α (γ * x) ∈ s at hγ
      simpa [map_mul] using hγ
    have h := huniq _ hγ'
    apply Subtype.ext
    change (γ : H) = α.symm δ
    rw [← h]
    simp

variable [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- A continuous automorphism `α` of `H` preserving a subgroup `Γ` that has a measurable strict
fundamental domain `s` with `0 < μ s < ∞` preserves the Haar measure `μ`. -/
theorem map_eq_self_of_preserves (Γ : Subgroup H) [Countable Γ] {s : Set H} (hsm : MeasurableSet s)
    (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s) (α : H ≃ₜ* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (μ : Measure H) [μ.IsHaarMeasure] (h0 : μ s ≠ 0) (htop : μ s ≠ ∞) :
    Measure.map α μ = μ := by
  have hfd : IsFundamentalDomain Γ s μ := IsFundamentalDomain.mk' hsm.nullMeasurableSet hs
  have hpre : IsFundamentalDomain Γ (α ⁻¹' s) μ :=
    IsFundamentalDomain.mk' (α.continuous.measurable hsm).nullMeasurableSet
      (existsUnique_mem_preimage Γ hs α.toMulEquiv hα)
  have hc := Measure.isMulLeftInvariant_eq_smul (Measure.map α μ) μ
  have hmass : Measure.map α μ s = μ s := by
    rw [Measure.map_apply (show Measurable (α : H → H) from α.continuous.measurable) hsm]
    exact hpre.measure_eq hfd
  rw [hc] at hmass
  have h1 : ((Measure.haarScalarFactor (Measure.map α μ) μ : NNReal) : ℝ≥0∞) = 1 := by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hmass
    exact (ENNReal.mul_eq_right h0 htop).mp hmass
  rw [hc, ENNReal.coe_eq_one.mp h1, one_smul]

/-- The same for any positive finite multiple of a Haar measure. -/
theorem measurePreserving_of_preserves (Γ : Subgroup H) [Countable Γ] {s : Set H} (hsm : MeasurableSet s)
    (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s) (α : H ≃ₜ* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (μ : Measure H) [μ.IsHaarMeasure] (h0 : μ s ≠ 0) (htop : μ s ≠ ∞) (c : ℝ≥0∞) :
    MeasurePreserving α (c • μ) (c • μ) := by
  refine ⟨α.continuous.measurable, ?_⟩
  rw [Measure.map_smul, map_eq_self_of_preserves Γ hsm hs α hα μ h0 htop]
  exact α.continuous.measurable.aemeasurable

end Automorphism

end Langlands.Global.EisensteinConstantTerm
