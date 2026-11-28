import Langlands.Analysis.CoordinateWavePacketPairing

/-! # Compact spectral support and the pairing of Fourier-integrated packets -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal

namespace Langlands.Analysis

/-- Uniform bounds on the squared norms of the fibres imply joint square integrability
when the parameter measure is finite. -/
theorem memLp_two_of_uniform_slice {X Q : Type*} [MeasurableSpace X] [MeasurableSpace Q]
    {α : Measure X} [IsFiniteMeasure α] {μ : Measure Q} [SFinite μ] {f : X × Q → ℂ}
    (hf : AEStronglyMeasurable f (α.prod μ)) (B : ℝ)
    (hB : ∀ᵐ x ∂α, MemLp (fun q => f (x, q)) 2 μ ∧ (∫ q, ‖f (x, q)‖ ^ 2 ∂μ) ≤ B) :
    MemLp f 2 (α.prod μ) := by
  have hm := hf.norm.pow 2
  refine (memLp_two_iff_integrable_sq_norm hf).mpr ((integrable_prod_iff hm).mpr ⟨?_, ?_⟩)
  · filter_upwards [hB] with x hx
    exact (memLp_two_iff_integrable_sq_norm hx.1.aestronglyMeasurable).mp hx.1
  · refine (integrable_const B).mono' hm.norm.integral_prod_right' ?_
    filter_upwards [hB] with x hx
    change ‖∫ q, ‖‖f (x, q)‖ ^ 2‖ ∂μ‖ ≤ B
    simpa only [Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] using hx.2

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure (Fin n → ℝ))

/-- A finite family with uniform fibre bounds can be multiplied by continuous weights
and summed on its compact parameter set. -/
theorem memLp_two_compact_weighted_sum {n k : ℕ} {Q : Type*} [MeasurableSpace Q]
    {μ : Measure Q} [SFinite μ] {C : Set Z[n]} (hC : IsCompact C)
    {f : Fin k → Z[n] × Q → ℂ} {c : Fin k → Z[n] → ℂ}
    (hc : ∀ j, Continuous (c j))
    (hf : ∀ j, AEStronglyMeasurable (f j) ((ζ[n].restrict C).prod μ))
    (hB : ∀ j, ∃ B : ℝ, ∀ x ∈ C,
      MemLp (fun q => f j (x, q)) 2 μ ∧ (∫ q, ‖f j (x, q)‖ ^ 2 ∂μ) ≤ B) :
    MemLp (fun p => ∑ j, c j p.1 * f j p) 2 ((ζ[n].restrict C).prod μ) := by
  let : IsFiniteMeasure (ζ[n].restrict C) := ⟨by simpa using hC.measure_lt_top (μ := ζ[n])⟩
  refine memLp_finsetSum _ fun j _ => ?_
  obtain ⟨B, hBj⟩ := hB j
  have hCae := ae_restrict_mem (μ := ζ[n]) hC.measurableSet
  have hf₂ := memLp_two_of_uniform_slice (hf j) B (hCae.mono fun x hx => hBj x hx)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hc j).continuousOn
  have hctop : MemLp (fun p : Z[n] × Q => c j p.1) ∞ ((ζ[n].restrict C).prod μ) :=
    memLp_top_of_bound ((hc j).measurable.comp measurable_fst).aestronglyMeasurable M
      ((Measure.quasiMeasurePreserving_fst (μ := ζ[n].restrict C) (ν := μ)).ae
        (hCae.mono fun x hx => hM x hx))
  exact hctop.mul hf₂

variable {n u m : ℕ} {Q : Type*} [MeasurableSpace Q]

/-- The positive phase at central frequency `z` and centre coordinate `y`. -/
def coordinatePhase (z y : Z[m]) : ℂ :=
  Complex.exp ((↑(∑ j, z j * y j) : ℂ) * Complex.I)

private theorem continuous_coordinatePhase (y : Z[m]) : Continuous (fun z => coordinatePhase z y) := by
  unfold coordinatePhase
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const)).mul continuous_const)

private theorem norm_coordinatePhase (z y : Z[m]) : ‖coordinatePhase z y‖ = 1 := by
  simp [coordinatePhase, Complex.norm_exp, Complex.mul_re]

/-- Fourier integration in the central coordinate of a full spectral chart, with the
Lebesgue measure in the original coordinates. -/
def compactSpectralPacket (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (f : Z[n] × Q → ℂ)
    (p : Z[m] × Q) : ℂ :=
  ∫ x, coordinatePhase (A.symm x).2 p.1 * f (x, p.2) ∂ζ[n]

private theorem memLp_of_restrict_left {μ : Measure Q} [SFinite μ] {C : Set Z[n]}
    {f : Z[n] × Q → ℂ} (hC : MeasurableSet C) (hf : MemLp f 2 ((ζ[n].restrict C).prod μ))
    (h0 : ∀ x ∉ C, ∀ q, f (x, q) = 0) : MemLp f 2 (ζ[n].prod μ) := by
  rw [Measure.restrict_prod_eq_prod_univ, ← memLp_indicator_iff_restrict
    (hC.prod MeasurableSet.univ).nullMeasurableSet] at hf
  have he : (C ×ˢ (Set.univ : Set Q)).indicator f = f := by
    ext p
    by_cases hp : p.1 ∈ C
    · exact Set.indicator_of_mem (Set.mk_mem_prod hp (Set.mem_univ _)) _
    · rw [Set.indicator_of_notMem (fun h => hp h.1), h0 p.1 hp p.2]
  rwa [he] at hf

private theorem ae_eq_compactSpectralPacket {μ : Measure Q} [SFinite μ]
    {α : Measure Z[u]} [SFinite α] (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n])
    (hA : MeasurePreserving A (α.prod ζ[m]) ζ[n]) {C : Set Z[n]}
    (hC : IsCompact C) {f : Z[n] × Q → ℂ} (hf : MemLp f 2 (ζ[n].prod μ))
    (h0 : ∀ x ∉ C, ∀ q, f (x, q) = 0) (U : Set Z[u])
    (hU : ∀ x ∈ C, (A.symm x).1 ∈ U) :
    compactSpectralPacket A f =ᵐ[ζ[m].prod μ]
      coordinateWavePacket (α.restrict U) (fun p : Z[u] × (Z[m] × Q) => f (A (p.1, p.2.1), p.2.2)) := by
  let e := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hq : ∀ᵐ q ∂μ, Integrable (fun x => f (x, q)) ζ[n] := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae] with q hm hi
    have h₂ := (memLp_two_iff_integrable_sq_norm hm).mpr hi
    exact memLp_one_iff_integrable.mp
      (h₂.mono_exponent_of_measure_support_ne_top (fun x hx => h0 x hx q)
        hC.measure_lt_top.ne (by norm_num))
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ζ[m]) (ν := μ)).ae hq] with p hp
  have hphase : AEStronglyMeasurable (fun x => coordinatePhase (A.symm x).2 p.1) ζ[n] :=
    ((continuous_coordinatePhase p.1).comp (continuous_snd.comp
      A.symm.toContinuousLinearEquiv.continuous)).aestronglyMeasurable
  have hin := hp.bdd_mul hphase (Filter.Eventually.of_forall fun x => (norm_coordinatePhase _ _).le)
  have hinA := hA.integrable_comp_of_integrable hin
  rw [compactSpectralPacket, ← hA.integral_comp e.measurableEmbedding]
  have hprod := integral_prod_symm _ hinA
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  unfold coordinateWavePacket coordinatePartialFourier coordinateFourierIntegral
  apply integral_congr_ae
  filter_upwards with z
  simp only [LinearEquiv.symm_apply_apply, coordinatePhase]
  rw [integral_const_mul]
  congr 1
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => h0 (A (v, z))
    (fun hx => hv (by simpa using hU (A (v, z)) hx)) p.2)).symm

private theorem compactSpectralPacket_input {μ : Measure Q} [SFinite μ]
    {α : Measure Z[u]} [SFinite α] (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n])
    (hA : MeasurePreserving A (α.prod ζ[m]) ζ[n]) {C : Set Z[n]} (hC : IsCompact C)
    {f : Z[n] × Q → ℂ} (hf : MemLp f 2 ((ζ[n].restrict C).prod μ))
    (h0 : ∀ x ∉ C, ∀ q, f (x, q) = 0) :
    ∃ U : Set Z[u], IsCompact U ∧ ∃ S : Set Z[m], IsCompact S ∧
      (∀ v ∉ U, ∀ z q, f (A (v, z), q) = 0) ∧ (∀ z ∉ S, ∀ v q, f (A (v, z), q) = 0) ∧
      MemLp (fun p : Z[u] × (Z[m] × Q) => f (A (p.1, p.2.1), p.2.2)) 2
        ((α.restrict U).prod (ζ[m].prod μ)) ∧
      compactSpectralPacket A f =ᵐ[ζ[m].prod μ]
        coordinateWavePacket (α.restrict U) (fun p : Z[u] × (Z[m] × Q) => f (A (p.1, p.2.1), p.2.2)) := by
  let U := (Prod.fst ∘ A.symm) '' C
  let S := (Prod.snd ∘ A.symm) '' C
  have hcA := A.symm.toContinuousLinearEquiv.continuous
  have hU : IsCompact U := hC.image (continuous_fst.comp hcA)
  have hS : IsCompact S := hC.image (continuous_snd.comp hcA)
  have hf' := memLp_of_restrict_left hC.measurableSet hf h0
  have hch := (hA.prod (MeasurePreserving.id μ)).comp
    ((measurePreserving_prodAssoc α ζ[m] μ).symm (e := MeasurableEquiv.prodAssoc))
  refine ⟨U, hU, S, hS, ?_, ?_, ?_, ?_⟩
  · intro v hv z q
    exact h0 _ (fun hx => hv ⟨A (v, z), hx, by simp⟩) _
  · intro z hz v q
    exact h0 _ (fun hx => hz ⟨A (v, z), hx, by simp⟩) _
  · exact (hf'.comp_measurePreserving hch).mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  · exact ae_eq_compactSpectralPacket A hA hC hf' h0 U fun x hx => ⟨x, hx, rfl⟩

/-- Two compactly supported spectral families with square-integrable restrictions give
square-integrable packets and an integrable pairing on the equal-central-frequency space. -/
def CompactSpectralPacketPairingStatement : Prop :=
  ∀ {n n' u v m : ℕ} {Q : Type*} [MeasurableSpace Q]
    (α : Measure Z[u]) (β : Measure Z[v]) (μ : Measure Q)
    [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure β] [SFinite μ]
    (A : (Z[u] × Z[m]) ≃ₗ[ℝ] Z[n]) (A' : (Z[v] × Z[m]) ≃ₗ[ℝ] Z[n']),
    MeasurePreserving A (α.prod ζ[m]) ζ[n] → MeasurePreserving A' (β.prod ζ[m]) ζ[n'] →
    ∀ (C : Set Z[n]) (C' : Set Z[n']) (f : Z[n] × Q → ℂ) (g : Z[n'] × Q → ℂ),
    IsCompact C → IsCompact C' →
    MemLp f 2 ((ζ[n].restrict C).prod μ) → MemLp g 2 ((ζ[n'].restrict C').prod μ) →
    (∀ x ∉ C, ∀ q, f (x, q) = 0) → (∀ x ∉ C', ∀ q, g (x, q) = 0) →
    let pairAt (z : Z[m]) (a : Z[u]) (b : Z[v]) :=
      ∫ q, f (A (a, z), q) * (starRingEnd ℂ) (g (A' (b, z), q)) ∂μ
    MemLp (compactSpectralPacket A f) 2 (ζ[m].prod μ) ∧
    MemLp (compactSpectralPacket A' g) 2 (ζ[m].prod μ) ∧
    Integrable (fun p : Z[m] × (Z[u] × Z[v]) => pairAt p.1 p.2.1 p.2.2) (ζ[m].prod (α.prod β)) ∧
    (∫ p, compactSpectralPacket A f p * (starRingEnd ℂ) (compactSpectralPacket A' g p)
      ∂(ζ[m].prod μ)) = ((2 * Real.pi : ℝ) ^ m : ℂ) *
      ∫ z, ∫ a, ∫ b, pairAt z a b ∂β ∂α ∂ζ[m]

/-- Apply the equal-frequency pairing on the compact noncentral projections of the supports. -/
theorem compactSpectralPacketPairing : CompactSpectralPacketPairingStatement := by
  intro n n' u v m Q _ α β μ _ _ _ A A' hA hA' C C' f g hC hC' hf hg hf0 hg0 pairAt
  obtain ⟨U, hU, S, hS, hfU, hfS, hf₂, hPf⟩ := compactSpectralPacket_input A hA hC hf hf0
  obtain ⟨V, hV, S', hS', hgV, hgS, hg₂, hPg⟩ := compactSpectralPacket_input A' hA' hC' hg hg0
  let : IsFiniteMeasure (α.restrict U) := ⟨by simpa using hU.measure_lt_top (μ := α)⟩
  let : IsFiniteMeasure (β.restrict V) := ⟨by simpa using hV.measure_lt_top (μ := β)⟩
  obtain ⟨hP, hP', hI, hEq⟩ := coordinateWavePacketPairing (α.restrict U) (β.restrict V) μ
    (fun p => f (A (p.1, p.2.1), p.2.2)) (fun p => g (A' (p.1, p.2.1), p.2.2)) S S'
      hS.measure_lt_top hS'.measure_lt_top hf₂ hg₂ hfS hgS
  have hpairU (z : Z[m]) (a : Z[u]) (ha : a ∉ U) (b : Z[v]) : pairAt z a b = 0 := by
    simp [pairAt, hfU a ha]
  have hpairV (z : Z[m]) (a : Z[u]) (b : Z[v]) (hb : b ∉ V) : pairAt z a b = 0 := by
    simp [pairAt, hgV b hb]
  refine ⟨(memLp_congr_ae hPf).mpr hP, (memLp_congr_ae hPg).mpr hP', ?_, ?_⟩
  · have hIon : IntegrableOn (fun p : Z[m] × (Z[u] × Z[v]) => pairAt p.1 p.2.1 p.2.2)
        (Set.univ ×ˢ (U ×ˢ V)) (ζ[m].prod (α.prod β)) := by
      simpa [IntegrableOn, ← Measure.prod_restrict, ← Measure.prod_restrict U V] using hI
    apply hIon.integrable_of_forall_notMem_eq_zero
    intro p hp
    by_cases ha : p.2.1 ∈ U
    · exact hpairV p.1 p.2.1 p.2.2 (fun hb => hp ⟨Set.mem_univ _, ha, hb⟩)
    · exact hpairU p.1 p.2.1 ha p.2.2
  · calc
      _ = _ := (integral_congr_ae (hPf.mul (hPg.fun_comp (starRingEnd ℂ)))).trans hEq
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards with z
        have hVeq (a : Z[u]) : (∫ b in V, pairAt z a b ∂β) = ∫ b, pairAt z a b ∂β :=
          setIntegral_eq_integral_of_forall_compl_eq_zero (hpairV z a)
        change (∫ a in U, ∫ b in V, pairAt z a b ∂β ∂α) = ∫ a, ∫ b, pairAt z a b ∂β ∂α
        simp_rw [hVeq]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun a ha => by simp [hpairU z a ha])

end Langlands.Analysis
