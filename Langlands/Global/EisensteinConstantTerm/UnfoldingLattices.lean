import Langlands.Global.EisensteinConstantTerm.UnfoldingSemidirect
import Langlands.Global.AdelicLeviFiniteVolume
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Retractions of closed semidirect decompositions and normalized Haar measures -/

noncomputable section

universe u v w

open MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

section Retraction

variable {N : Type u} {M : Type v} {H : Type w} [Group N] [Group M] [Group H]
  [TopologicalSpace M] [IsTopologicalGroup M] [SigmaCompactSpace M]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- **Continuity of the retraction of a closed semidirect decomposition.** Let `i : N → H` and
`j : M → H` be homomorphisms, `j` continuous and injective, with `i(N)` a closed normal subgroup
meeting `j(M)` trivially, and with `H = i(N) j(M)`. If `M` is σ-compact and `H` is locally
compact and Hausdorff, the retraction `H → M` with kernel `i(N)` is a continuous homomorphism.
The bijection `M → H / i(N)` is open by the open mapping theorem. -/
theorem exists_continuous_retraction (i : N →* H) (j : M →* H) (hj : Continuous j)
    (hnormal : i.range.Normal) (hclosed : IsClosed (i.range : Set H))
    (hdec : ∀ h, ∃ n m, i n * j m = h) (hdisj : ∀ m, j m ∈ i.range → m = 1) :
    ∃ p : H →* M, Continuous p ∧ (∀ m, p (j m) = m) ∧ (∀ n, p (i n) = 1) ∧
      (∀ h, p h = 1 → ∃ n, i n = h) := by
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup H, K = i.range := ⟨_, rfl⟩
  have hmemK : ∀ n, i n ∈ K := fun n => hKdef ▸ MonoidHom.mem_range.mpr ⟨n, rfl⟩
  have hKmem : ∀ h ∈ K, ∃ n, i n = h := fun h hh => (hKdef ▸ hh : h ∈ i.range)
  have : K.Normal := hKdef ▸ hnormal
  have : IsClosed (K : Set H) := hKdef ▸ hclosed
  have : T2Space (H ⧸ K) := inferInstance
  have : BaireSpace (H ⧸ K) := inferInstance
  let φ : M →* H ⧸ K := (QuotientGroup.mk' K).comp j
  have hφc : Continuous φ := continuous_quot_mk.comp hj
  have hφs : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H h =>
      obtain ⟨n, m, rfl⟩ := hdec h
      refine ⟨m, ?_⟩
      change (QuotientGroup.mk (j m) : H ⧸ K) = QuotientGroup.mk (i n * j m)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (i n)).mpr (hmemK n), one_mul]
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    exact hdisj m (hKdef ▸ (QuotientGroup.eq_one_iff (j m)).mp hm)
  have hφo : IsOpenMap φ := MonoidHom.isOpenMap_of_sigmaCompact φ hφs hφc
  let e : M ≃* H ⧸ K := MulEquiv.ofBijective φ ⟨hφi, hφs⟩
  let eh : M ≃ₜ H ⧸ K := e.toEquiv.toHomeomorphOfContinuousOpen hφc hφo
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' K), ?_, ?_, ?_, ?_⟩
  · exact eh.symm.continuous.comp continuous_quot_mk
  · intro m
    change e.symm (φ m) = m
    exact e.symm_apply_apply m
  · intro n
    change e.symm (QuotientGroup.mk (i n)) = 1
    rw [(QuotientGroup.eq_one_iff (i n)).mpr (hmemK n), map_one]
  · intro h hh
    change e.symm (QuotientGroup.mk h) = 1 at hh
    have : (QuotientGroup.mk h : H ⧸ K) = 1 := by
      rw [← e.apply_symm_apply (QuotientGroup.mk h), hh, map_one]
    exact hKmem h ((QuotientGroup.eq_one_iff h).mp this)

end Retraction

section Normalized

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Haar measure scaled by the reciprocal of the Haar measure of the chosen fundamental domain of
a discrete subgroup. When this covolume is finite the fundamental domain has mass one
(`normalizedHaar_fundamentalDomain`); when it is infinite the scaling factor is `0` and this is
the zero measure. -/
def normalizedHaar (Δ : Subgroup X) (hΔ : IsDiscrete (Δ : Set X)) : Measure X :=
  ((Measure.haar : Measure X) (fundamentalDomain Δ hΔ))⁻¹ • Measure.haar

variable (Δ : Subgroup X) (hΔ : IsDiscrete (Δ : Set X))
  {K : Set X} (hK : IsCompact K) (hKcover : ∀ x, ∃ γ ∈ Δ, γ * x ∈ K)

include hK hKcover in
theorem isFiniteMeasure_haarQuotientMeasure_of_cover :
    IsFiniteMeasure (haarQuotientMeasure Δ hΔ) :=
  isFiniteMeasure_haarQuotientMeasure_of_isCompact Δ hΔ hK hKcover

include hK hKcover in
theorem haar_fundamentalDomain_ne_top_of_cover :
    (Measure.haar : Measure X) (fundamentalDomain Δ hΔ) ≠ ∞ :=
  haveI := isFiniteMeasure_haarQuotientMeasure_of_cover Δ hΔ hK hKcover
  haar_fundamentalDomain_ne_top Δ hΔ

include hK hKcover in
theorem inv_haar_mul_haar_fundamentalDomain :
    ((Measure.haar : Measure X) (fundamentalDomain Δ hΔ))⁻¹ *
      (Measure.haar : Measure X) (fundamentalDomain Δ hΔ) = 1 :=
  ENNReal.inv_mul_cancel (haar_fundamentalDomain_ne_zero Δ hΔ)
    (haar_fundamentalDomain_ne_top_of_cover Δ hΔ hK hKcover)

include hK hKcover in
theorem normalizedHaar_fundamentalDomain :
    normalizedHaar Δ hΔ (fundamentalDomain Δ hΔ) = 1 := by
  rw [normalizedHaar, Measure.smul_apply, smul_eq_mul]
  exact inv_haar_mul_haar_fundamentalDomain Δ hΔ hK hKcover

include hK hKcover in
theorem isHaarMeasure_normalizedHaar : (normalizedHaar Δ hΔ).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr
      (haar_fundamentalDomain_ne_top_of_cover Δ hΔ hK hKcover))
    (ENNReal.inv_ne_top.mpr (haar_fundamentalDomain_ne_zero Δ hΔ))

include hK hKcover in
theorem isMulRightInvariant_normalizedHaar : (normalizedHaar Δ hΔ).IsMulRightInvariant := by
  have := isFiniteMeasure_haarQuotientMeasure_of_cover Δ hΔ hK hKcover
  have := isMulRightInvariant_haar_of_isFiniteMeasure Δ hΔ
  unfold normalizedHaar
  infer_instance

theorem regular_normalizedHaar [T2Space X] : (normalizedHaar Δ hΔ).Regular := by
  unfold normalizedHaar
  exact Measure.Regular.smul (ENNReal.inv_ne_top.mpr (haar_fundamentalDomain_ne_zero Δ hΔ))

instance isMulLeftInvariant_normalizedHaar : (normalizedHaar Δ hΔ).IsMulLeftInvariant := by
  unfold normalizedHaar
  infer_instance

instance sFinite_normalizedHaar : SFinite (normalizedHaar Δ hΔ) := by
  unfold normalizedHaar
  infer_instance

omit [IsTopologicalGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
include hK hKcover in
/-- A compact set meeting every orbit of `Δ` is carried by a continuous surjective homomorphism
onto a compact set meeting every orbit of any subgroup containing the image of `Δ`. -/
theorem exists_cover_of_map {Y : Type v} [Group Y] [TopologicalSpace Y]
    (q : X →* Y) (hq : Continuous q) (hqs : Function.Surjective q)
    (ΔY : Subgroup Y) (hqΔ : ∀ γ ∈ Δ, q γ ∈ ΔY) :
    ∃ K' : Set Y, IsCompact K' ∧ ∀ y, ∃ γ ∈ ΔY, γ * y ∈ K' := by
  refine ⟨q '' K, hK.image hq, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hqs y
  obtain ⟨γ, hγ, hγK⟩ := hKcover x
  exact ⟨q γ, hqΔ γ hγ, ⟨γ * x, hγK, map_mul q γ x⟩⟩

end Normalized


section Characterization

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (Δ : Subgroup X) (hΔ : IsDiscrete (Δ : Set X))

/-- A left invariant measure, finite on compacts, that gives mass one to a measurable
transversal of the discrete subgroup `Δ` is `normalizedHaar Δ hΔ`. -/
theorem eq_normalizedHaar (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    {T : Set X} (hT : MeasurableSet T) (hTu : ∀ x, ∃! γ : Δ, (γ : X) * x ∈ T) (hμT : μ T = 1) :
    μ = normalizedHaar Δ hΔ := by
  have : Countable Δ := countable_of_isDiscrete Δ hΔ
  have h := Measure.isMulLeftInvariant_eq_smul μ (Measure.haar : Measure X)
  have hfdT : IsFundamentalDomain Δ T (Measure.haar : Measure X) :=
    IsFundamentalDomain.mk' hT.nullMeasurableSet hTu
  have hTeq : (Measure.haar : Measure X) T =
      (Measure.haar : Measure X) (fundamentalDomain Δ hΔ) :=
    hfdT.measure_eq (isFundamentalDomain Δ hΔ _)
  rw [h, Measure.smul_apply, hTeq, ENNReal.smul_def, smul_eq_mul] at hμT
  rw [normalizedHaar, h, ENNReal.smul_def, ENNReal.eq_inv_of_mul_eq_one_left hμT]

omit [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- A transversal of `Δ'` pulls back along an isomorphism carrying `Δ` onto `Δ'` to a
transversal of `Δ`. -/
theorem transversal_preimage {Y : Type v} [Group Y] (e : X ≃* Y) (Δ' : Subgroup Y)
    (he : ∀ x, e x ∈ Δ' ↔ x ∈ Δ) {T : Set Y} (hTu : ∀ y, ∃! γ : Δ', (γ : Y) * y ∈ T) (x : X) :
    ∃! γ : Δ, (γ : X) * x ∈ e ⁻¹' T := by
  obtain ⟨γ', hγ', hu⟩ := hTu (e x)
  have hmem : e.symm γ' ∈ Δ := (he _).mp (by simp)
  refine ⟨⟨e.symm γ', hmem⟩, ?_, ?_⟩
  · change e (e.symm γ' * x) ∈ T
    simpa using hγ'
  · intro δ hδ
    have hδ' : e δ ∈ Δ' := (he δ).mpr δ.property
    have h1 : (⟨e δ, hδ'⟩ : Δ') = γ' := hu _ (by simpa using hδ)
    apply Subtype.ext
    change (δ : X) = e.symm γ'
    rw [← h1]
    simp

variable {Y : Type v} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
  [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  (Δ' : Subgroup Y) (hΔ' : IsDiscrete (Δ' : Set Y))
  {K : Set X} (hK : IsCompact K) (hKcover : ∀ x, ∃ γ ∈ Δ, γ * x ∈ K)

omit [LocallyCompactSpace X] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- The image of the chosen fundamental domain of `Δ` is a transversal of `Δ'`. -/
theorem transversal_image (e : X ≃ₜ* Y) (he : ∀ x, e x ∈ Δ' ↔ x ∈ Δ) (y : Y) :
    ∃! γ : Δ', (γ : Y) * y ∈ e.symm ⁻¹' fundamentalDomain Δ hΔ := by
  refine transversal_preimage Δ' e.symm.toMulEquiv Δ (fun y => ?_)
    (fundamentalDomain_unique Δ hΔ) y
  constructor
  · intro h
    have := (he (e.symm y)).mpr h
    simpa using this
  · intro h
    change e.symm y ∈ Δ
    exact (he (e.symm y)).mp (by rw [e.apply_symm_apply]; exact h)

include hK hKcover in
/-- Normalized Haar measures correspond under a topological group isomorphism carrying one
discrete subgroup onto the other. -/
theorem map_normalizedHaar (e : X ≃ₜ* Y) (he : ∀ x, e x ∈ Δ' ↔ x ∈ Δ) :
    Measure.map e (normalizedHaar Δ hΔ) = normalizedHaar Δ' hΔ' := by
  have := isHaarMeasure_normalizedHaar Δ hΔ hK hKcover
  have hT : MeasurableSet (e.symm ⁻¹' fundamentalDomain Δ hΔ) :=
    e.symm.continuous.measurable (measurableSet_fundamentalDomain Δ hΔ)
  refine eq_normalizedHaar Δ' hΔ' _ hT (transversal_image Δ hΔ Δ' e he) ?_
  rw [Measure.map_apply (show Measurable (e : X → Y) from e.continuous.measurable) hT,
    show e ⁻¹' (e.symm ⁻¹' fundamentalDomain Δ hΔ) = fundamentalDomain Δ hΔ by
      ext x; simp]
  exact normalizedHaar_fundamentalDomain Δ hΔ hK hKcover

include hK hKcover in
/-- Integrals over fundamental domains correspond under a topological group isomorphism carrying
one discrete subgroup onto the other. -/
theorem setIntegral_fundamentalDomain_map (e : X ≃ₜ* Y) (he : ∀ x, e x ∈ Δ' ↔ x ∈ Δ)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Y → E)
    (hg : ∀ γ ∈ Δ', ∀ y, g (γ * y) = g y) :
    ∫ x in fundamentalDomain Δ hΔ, g (e x) ∂normalizedHaar Δ hΔ =
      ∫ y in fundamentalDomain Δ' hΔ', g y ∂normalizedHaar Δ' hΔ' := by
  have : Countable Δ' := countable_of_isDiscrete Δ' hΔ'
  set s := e.symm ⁻¹' fundamentalDomain Δ hΔ with hs
  have hsm : MeasurableSet s :=
    e.symm.continuous.measurable (measurableSet_fundamentalDomain Δ hΔ)
  have hpre : e.toHomeomorph.toMeasurableEquiv ⁻¹' s = fundamentalDomain Δ hΔ := by
    ext x
    change e.symm (e x) ∈ fundamentalDomain Δ hΔ ↔ x ∈ fundamentalDomain Δ hΔ
    rw [e.symm_apply_apply]
  have hfds : IsFundamentalDomain Δ' s (normalizedHaar Δ' hΔ') :=
    IsFundamentalDomain.mk' hsm.nullMeasurableSet (transversal_image Δ hΔ Δ' e he)
  calc ∫ x in fundamentalDomain Δ hΔ, g (e x) ∂normalizedHaar Δ hΔ
      = ∫ x in e.toHomeomorph.toMeasurableEquiv ⁻¹' s,
          g (e.toHomeomorph.toMeasurableEquiv x) ∂normalizedHaar Δ hΔ := by
        rw [hpre]; rfl
    _ = ∫ y in s, g y ∂Measure.map e.toHomeomorph.toMeasurableEquiv (normalizedHaar Δ hΔ) :=
        (setIntegral_map_equiv _ _ _).symm
    _ = ∫ y in s, g y ∂normalizedHaar Δ' hΔ' := by
        rw [← map_normalizedHaar Δ hΔ Δ' hΔ' hK hKcover e he]; rfl
    _ = _ := hfds.setIntegral_eq (isFundamentalDomain Δ' hΔ' _)
        (fun γ y => hg _ γ.property y)

end Characterization

end Langlands.Global.LeftCosetSpace
