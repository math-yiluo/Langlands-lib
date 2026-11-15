import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration

/-! # Exchanging two Iwasawa integrals of a Levi-invariant function

Let `M` normalize two subgroups `U` and `V` of a topological group `G`, and let `K` be an open
subgroup with `G = M U K = M V K` and `m u ∈ K ↔ m ∈ K ∧ u ∈ K`, `m v ∈ K ↔ m ∈ K ∧ v ∈ K`.
For a function `Θ` on `G` invariant under left translation by `M`, this module proves
`∫_K ∫_V Θ(v k) dv dk = ∫_K ∫_U Θ(u k) du dk`, first for `Θ ≥ 0` and then for complex `Θ`
under absolute integrability. The Haar measures of `M`, `U`, `V` give mass one to their
intersections with `K`, and the Haar measure of `M` is two-sided invariant.

The proof uses the Iwasawa formula `∫_G F = ∫_K ∫_M ∫_W F(m w k)` (Waldspurger I.1 (2)) with
the cutoffs `F = 1_{W K} Θ`. By the splitting hypothesis, `m w k ∈ W K ↔ m ∈ K`, so
`∫_G 1_{W K} Θ = ∫_K ∫_W Θ(w k)`. The integrals of `1_{V K} Θ` and `1_{U K} Θ` over `G` agree:
insert `∫_M 1_{U K}(m⁻¹ g) dm = 1`, exchange the integrals, substitute `g ↦ m g`, and use
`∫_M 1_{V K}(m g) dm = 1`.
-/

noncomputable section

open scoped ENNReal NNReal Pointwise Topology
open MeasureTheory Measure

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

section Iwasawa

variable {M W : Subgroup G} [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  (hMW : M ≤ Subgroup.normalizer (W : Set G))
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant]
  {μW : Measure W} [SFinite μW] [μW.IsMulLeftInvariant]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
include hMW in
/-- Left translations of `M W` are skew products in the coordinates `(m, w)`, for arbitrary
Borel structures on `M` and `W`. -/
theorem measurePreserving_shift (x₀ : M × W) :
    MeasurePreserving (leviUnipotentShift hMW x₀) (μM.prod μW) (μM.prod μW) :=
  (measurePreserving_mul_left μM x₀.1⁻¹).skew_product
    (continuous_leviUnipotentShift_snd hMW x₀).measurable
    (Filter.Eventually.of_forall fun _ => map_mul_left_eq_self _ _)

include hMW in
/-- The Iwasawa formula `∫_G F = ∫_K ∫_M ∫_W F(m w k)` of
`HarishChandraSchwartz.lintegral_eq_lintegral_levi_unipotent`, for arbitrary Borel structures
on `M` and `W`. -/
theorem lintegral_eq_iwasawa {K : Subgroup G} (hK : MeasurableSet (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ w : W, ∃ k ∈ K, g = (m : G) * w * k)
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (hWK : μW {w : W | (w : G) ∈ K} = 1)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ = ∫⁻ k in (K : Set G), ∫⁻ m, ∫⁻ w, F ((m : G) * w * k) ∂μW ∂μM ∂μ := by
  have hι : Measurable (leviUnipotentMul (M := M) (U := W)) :=
    continuous_leviUnipotentMul.measurable
  have h := CompactFactorization.lintegral_restrict_lintegral_mul μ K hK (μM.prod μW)
    leviUnipotentMul hι
    (fun g => by
      obtain ⟨m, w, k, hk, rfl⟩ := hfac g
      exact ⟨(m, w), k, hk, rfl⟩)
    (fun x₀ => ⟨leviUnipotentShift hMW x₀, measurePreserving_shift hMW x₀,
      fun x => leviUnipotentMul_shift hMW x₀ x⟩) F hF
  have hpre : leviUnipotentMul ⁻¹' (K : Set G) =
      {m : M | (m : G) ∈ K} ×ˢ {w : W | (w : G) ∈ K} := by
    ext x
    simp only [Set.mem_preimage, leviUnipotentMul, SetLike.mem_coe, Set.mem_prod,
      Set.mem_ofPred_eq]
    exact hsplit x.1 x.2
  rw [hpre, Measure.prod_prod, hMK, hWK, one_mul, one_mul] at h
  rw [← h]
  refine lintegral_congr fun k => ?_
  have hm : Measurable fun x : M × W => F (leviUnipotentMul x * k) :=
    hF.comp (hι.mul_const k)
  rw [lintegral_prod _ hm.aemeasurable]
  rfl

end Iwasawa

section Cutoff

variable {M W K : Subgroup G}

/-- The cutoff set `W K`. -/
def cutoffSet (W K : Subgroup G) : Set G :=
  (W : Set G) * (K : Set G)

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
/-- With the splitting `m w ∈ K ↔ m ∈ K ∧ w ∈ K`, `m w k ∈ W K ↔ m ∈ K` for `k ∈ K`. -/
theorem mem_cutoffSet_iff (hMW : M ≤ Subgroup.normalizer (W : Set G))
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (m : M) (w : W) {k : G} (hk : k ∈ K) :
    (m : G) * w * k ∈ cutoffSet W K ↔ (m : G) ∈ K := by
  constructor
  · rintro ⟨w', hw', k', hk', he⟩
    have hconj : (m : G)⁻¹ * w'⁻¹ * (m : G) ∈ W := by
      have h := (Subgroup.mem_normalizer_iff.mp (hMW (M.inv_mem m.2)) (w'⁻¹)).mp
        (W.inv_mem hw')
      simpa only [inv_inv] using h
    let w₀ : W := ⟨(m : G)⁻¹ * w'⁻¹ * (m : G) * w, W.mul_mem hconj w.2⟩
    have hmem : (m : G) * w₀ ∈ K := by
      have he' : (m : G) * w₀ = k' * k⁻¹ := by
        have : (m : G) * w * k = w' * k' := he.symm
        simp only [w₀]
        calc (m : G) * ((m : G)⁻¹ * w'⁻¹ * (m : G) * w)
            = w'⁻¹ * ((m : G) * w * k) * k⁻¹ := by group
          _ = w'⁻¹ * (w' * k') * k⁻¹ := by rw [this]
          _ = k' * k⁻¹ := by group
      rw [he']
      exact K.mul_mem hk' (K.inv_mem hk)
    exact ((hsplit m w₀).mp hmem).1
  · intro hm
    refine ⟨(m : G) * w * (m : G)⁻¹, ?_, (m : G) * k, K.mul_mem hm hk, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMW m.2) w).mp w.2

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem isOpen_cutoffSet (hK : IsOpen (K : Set G)) : IsOpen (cutoffSet W K) :=
  hK.mul_left

/-- The cutoff function `1_{W K}`. -/
def cutoff (W K : Subgroup G) (g : G) : ℝ≥0∞ :=
  (cutoffSet W K).indicator 1 g

omit [SecondCountableTopology G] in
theorem measurable_cutoff (hK : IsOpen (K : Set G)) : Measurable (cutoff W K) :=
  measurable_one.indicator (isOpen_cutoffSet hK).measurableSet

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem cutoff_mul (hMW : M ≤ Subgroup.normalizer (W : Set G))
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (m : M) (w : W) {k : G} (hk : k ∈ K) :
    cutoff W K ((m : G) * w * k) = {m : M | (m : G) ∈ K}.indicator 1 m := by
  unfold cutoff
  by_cases hm : (m : G) ∈ K
  · rw [Set.indicator_of_mem ((mem_cutoffSet_iff hMW hsplit m w hk).mpr hm),
      Set.indicator_of_mem (show m ∈ {m : M | (m : G) ∈ K} from hm)]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hm ((mem_cutoffSet_iff hMW hsplit m w hk).mp h)),
      Set.indicator_of_notMem (show m ∉ {m : M | (m : G) ∈ K} from hm)]

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant]
  {μW : Measure W} [SFinite μW] [μW.IsMulLeftInvariant]

omit [IsTopologicalGroup G] [SecondCountableTopology G] [SFinite μM] in
theorem measurableSet_leviCompact (hK : IsOpen (K : Set G)) :
    MeasurableSet {m : M | (m : G) ∈ K} :=
  continuous_subtype_val.measurable hK.measurableSet

/-- **The cutoff integral.** For `Θ ≥ 0` invariant under left translation by `M`,
`∫_G 1_{W K} Θ = ∫_K ∫_W Θ(w k)`. -/
theorem lintegral_cutoff_mul (hMW : M ≤ Subgroup.normalizer (W : Set G))
    (hK : IsOpen (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ w : W, ∃ k ∈ K, g = (m : G) * w * k)
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (hWK : μW {w : W | (w : G) ∈ K} = 1)
    (Θ : G → ℝ≥0∞) (hΘ : Measurable Θ) (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    ∫⁻ g, cutoff W K g * Θ g ∂μ = ∫⁻ k in (K : Set G), ∫⁻ w, Θ ((w : G) * k) ∂μW ∂μ := by
  rw [lintegral_eq_iwasawa hMW hK.measurableSet hfac hsplit hMK hWK
    (fun g => cutoff W K g * Θ g) ((measurable_cutoff hK).mul hΘ)]
  refine setLIntegral_congr_fun hK.measurableSet fun k hk => ?_
  have hinner : ∀ m : M, ∫⁻ w, cutoff W K ((m : G) * w * k) * Θ ((m : G) * w * k) ∂μW =
      {m : M | (m : G) ∈ K}.indicator (fun _ => ∫⁻ w, Θ ((w : G) * k) ∂μW) m := by
    intro m
    by_cases hm : (m : G) ∈ K
    · rw [Set.indicator_of_mem (show m ∈ {m : M | (m : G) ∈ K} from hm)]
      refine lintegral_congr fun w => ?_
      rw [cutoff_mul hMW hsplit m w hk, Set.indicator_of_mem
        (show m ∈ {m : M | (m : G) ∈ K} from hm), Pi.one_apply, one_mul, mul_assoc, hinv]
    · rw [Set.indicator_of_notMem (show m ∉ {m : M | (m : G) ∈ K} from hm)]
      refine (lintegral_congr fun w => ?_).trans lintegral_zero
      rw [cutoff_mul hMW hsplit m w hk, Set.indicator_of_notMem
        (show m ∉ {m : M | (m : G) ∈ K} from hm), zero_mul]
  simp_rw [hinner]
  rw [lintegral_indicator_const (measurableSet_leviCompact hK), hMK, mul_one]

omit [SecondCountableTopology G] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [SFinite μM] in
/-- The left `M`-average of `1_{W K}` is one: `∫_M 1_{W K}(m⁻¹ g) dm = 1`. -/
theorem lintegral_cutoff_inv_mul (hMW : M ≤ Subgroup.normalizer (W : Set G))
    (hK : IsOpen (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ w : W, ∃ k ∈ K, g = (m : G) * w * k)
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (g : G) :
    ∫⁻ m : M, cutoff W K ((m : G)⁻¹ * g) ∂μM = 1 := by
  obtain ⟨m₀, w, k, hk, rfl⟩ := hfac g
  have he : ∀ m : M, cutoff W K ((m : G)⁻¹ * ((m₀ : G) * w * k)) =
      ((fun m => m₀⁻¹ * m) ⁻¹' {m : M | (m : G) ∈ K}).indicator 1 m := by
    intro m
    have h1 : (m : G)⁻¹ * ((m₀ : G) * w * k) = ((m⁻¹ * m₀ : M) : G) * w * k := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [h1, cutoff_mul hMW hsplit _ w hk]
    by_cases hm : ((m⁻¹ * m₀ : M) : G) ∈ K
    · have hm' : m ∈ (fun m => m₀⁻¹ * m) ⁻¹' {m : M | (m : G) ∈ K} := by
        have := K.inv_mem hm
        simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.coe_mul,
          InvMemClass.coe_inv, mul_inv_rev, inv_inv] using this
      rw [Set.indicator_of_mem (show m⁻¹ * m₀ ∈ {m : M | (m : G) ∈ K} from hm),
        Set.indicator_of_mem hm']
      rfl
    · have hm' : m ∉ (fun m => m₀⁻¹ * m) ⁻¹' {m : M | (m : G) ∈ K} := by
        intro h
        apply hm
        have := K.inv_mem (show ((m₀⁻¹ * m : M) : G) ∈ K from h)
        simpa only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv] using this
      rw [Set.indicator_of_notMem (show m⁻¹ * m₀ ∉ {m : M | (m : G) ∈ K} from hm),
        Set.indicator_of_notMem hm']
  simp_rw [he]
  rw [lintegral_indicator_one ((measurable_const_mul _) (measurableSet_leviCompact hK)),
    measure_preimage_mul, hMK]

omit [SecondCountableTopology G] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [SFinite μM] [μM.IsMulLeftInvariant] in
/-- The right `M`-average of `1_{W K}` is one: `∫_M 1_{W K}(m g) dm = 1`, by right invariance
of the Haar measure of `M`. -/
theorem lintegral_cutoff_mul_left [μM.IsMulRightInvariant]
    (hMW : M ≤ Subgroup.normalizer (W : Set G))
    (hK : IsOpen (K : Set G))
    (hfac : ∀ g : G, ∃ m : M, ∃ w : W, ∃ k ∈ K, g = (m : G) * w * k)
    (hsplit : ∀ (m : M) (w : W), (m : G) * w ∈ K ↔ (m : G) ∈ K ∧ (w : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) (g : G) :
    ∫⁻ m : M, cutoff W K ((m : G) * g) ∂μM = 1 := by
  obtain ⟨m₀, w, k, hk, rfl⟩ := hfac g
  have he : ∀ m : M, cutoff W K ((m : G) * ((m₀ : G) * w * k)) =
      ((fun m => m * m₀) ⁻¹' {m : M | (m : G) ∈ K}).indicator 1 m := by
    intro m
    have h1 : (m : G) * ((m₀ : G) * w * k) = ((m * m₀ : M) : G) * w * k := by
      simp only [Subgroup.coe_mul]
      group
    rw [h1, cutoff_mul hMW hsplit _ w hk]
    rfl
  simp_rw [he]
  rw [lintegral_indicator_one ((measurable_mul_const _) (measurableSet_leviCompact hK)),
    measure_preimage_mul_right, hMK]

end Cutoff

section Exchange

variable {M U V K : Subgroup G} [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology U] [SecondCountableTopology V]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant] [μM.IsMulRightInvariant]
  {μU : Measure U} [SFinite μU] [μU.IsMulLeftInvariant]
  {μV : Measure V} [SFinite μV] [μV.IsMulLeftInvariant]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology U] [SecondCountableTopology V] in
/-- **Exchange of the two cutoff integrals.** For `Θ ≥ 0` invariant under left translation
by `M`, `∫_G 1_{V K} Θ = ∫_G 1_{U K} Θ`. -/
theorem lintegral_cutoff_exchange (hK : IsOpen (K : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hfacU : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hsplitU : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hfacV : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (hsplitV : ∀ (m : M) (v : V), (m : G) * v ∈ K ↔ (m : G) ∈ K ∧ (v : G) ∈ K)
    (hMK : μM {m : M | (m : G) ∈ K} = 1)
    (Θ : G → ℝ≥0∞) (hΘ : Measurable Θ) (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    ∫⁻ g, cutoff V K g * Θ g ∂μ = ∫⁻ g, cutoff U K g * Θ g ∂μ := by
  have hcU := measurable_cutoff (W := U) hK
  have hcV := measurable_cutoff (W := V) hK
  have hval : Measurable fun m : M => (m : G) := continuous_subtype_val.measurable
  have hmeas1 : Measurable (Function.uncurry fun (g : G) (m : M) =>
      cutoff V K g * Θ g * cutoff U K ((m : G)⁻¹ * g)) :=
    ((hcV.comp measurable_fst).mul (hΘ.comp measurable_fst)).mul
      (hcU.comp ((hval.comp measurable_snd).inv.mul measurable_fst))
  have hmeas2 : Measurable (Function.uncurry fun (g : G) (m : M) =>
      cutoff V K ((m : G) * g) * Θ g * cutoff U K g) :=
    ((hcV.comp ((hval.comp measurable_snd).mul measurable_fst)).mul
      (hΘ.comp measurable_fst)).mul (hcU.comp measurable_fst)
  calc ∫⁻ g, cutoff V K g * Θ g ∂μ
      = ∫⁻ g, ∫⁻ m : M, cutoff V K g * Θ g * cutoff U K ((m : G)⁻¹ * g) ∂μM ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (cutoff V K g * Θ g)
            (f := fun m : M => cutoff U K ((m : G)⁻¹ * g))
            (hcU.comp (hval.inv.mul measurable_const)),
          lintegral_cutoff_inv_mul (μM := μM) hMU hK hfacU hsplitU hMK g, mul_one]
    _ = ∫⁻ m : M, ∫⁻ g, cutoff V K g * Θ g * cutoff U K ((m : G)⁻¹ * g) ∂μ ∂μM :=
        lintegral_lintegral_swap hmeas1.aemeasurable
    _ = ∫⁻ m : M, ∫⁻ g, cutoff V K ((m : G) * g) * Θ g * cutoff U K g ∂μ ∂μM := by
        refine lintegral_congr fun m => ?_
        rw [← lintegral_mul_left_eq_self _ (m : G)]
        refine lintegral_congr fun g => ?_
        rw [hinv, inv_mul_cancel_left]
    _ = ∫⁻ g, ∫⁻ m : M, cutoff V K ((m : G) * g) * Θ g * cutoff U K g ∂μM ∂μ :=
        (lintegral_lintegral_swap hmeas2.aemeasurable).symm
    _ = ∫⁻ g, cutoff U K g * Θ g ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const (cutoff U K g)
            (f := fun m : M => cutoff V K ((m : G) * g) * Θ g)
            ((hcV.comp (hval.mul measurable_const)).mul measurable_const),
          lintegral_mul_const (Θ g) (f := fun m : M => cutoff V K ((m : G) * g))
            (hcV.comp (hval.mul measurable_const)),
          lintegral_cutoff_mul_left (μM := μM) hMV hK hfacV hsplitV hMK g, one_mul, mul_comm]

/-- **Exchange of opposite Iwasawa integrals, nonnegative form.** For `Θ ≥ 0` invariant under
left translation by `M`, `∫_K ∫_V Θ(v k) dv dk = ∫_K ∫_U Θ(u k) du dk`. -/
theorem lintegral_exchange (hK : IsOpen (K : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hfacU : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hsplitU : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hfacV : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (hsplitV : ∀ (m : M) (v : V), (m : G) * v ∈ K ↔ (m : G) ∈ K ∧ (v : G) ∈ K)
    (hVK : μV {v : V | (v : G) ∈ K} = 1)
    (hMK : μM {m : M | (m : G) ∈ K} = 1)
    (Θ : G → ℝ≥0∞) (hΘ : Measurable Θ) (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    ∫⁻ k in (K : Set G), ∫⁻ v, Θ ((v : G) * k) ∂μV ∂μ =
      ∫⁻ k in (K : Set G), ∫⁻ u, Θ ((u : G) * k) ∂μU ∂μ := by
  rw [← lintegral_cutoff_mul hMV hK hfacV hsplitV hMK hVK Θ hΘ hinv,
    ← lintegral_cutoff_mul hMU hK hfacU hsplitU hMK hUK Θ hΘ hinv]
  exact lintegral_cutoff_exchange (μM := μM) hK hMU hfacU hsplitU hMV hfacV hsplitV hMK Θ hΘ hinv

end Exchange

section Complex

/-- The orbit space `M \ G` of left translations by `M`, with the quotient σ-algebra. -/
abbrev LeviQuotient (M : Subgroup G) : Type u :=
  Quotient (QuotientGroup.rightRel M)

/-- The projection `G → M \ G`. -/
def leviQuotientMk (M : Subgroup G) (g : G) : LeviQuotient M :=
  Quotient.mk'' g

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
theorem leviQuotientMk_mul (M : Subgroup G) (m : M) (g : G) :
    leviQuotientMk M ((m : G) * g) = leviQuotientMk M g :=
  Quotient.sound (QuotientGroup.rightRel_apply.mpr (by
    rw [mul_inv_rev, mul_inv_cancel_left]
    exact M.inv_mem m.2))

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] in
theorem measurable_leviQuotientMk (M : Subgroup G) : Measurable (leviQuotientMk M) :=
  measurable_quotient_mk''

/-- A function on `G` invariant under left translation by `M`, as a function on `M \ G`. -/
def leviQuotientLift (M : Subgroup G) {β : Type*} (Θ : G → β)
    (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) : LeviQuotient M → β :=
  Quotient.lift Θ fun a b hab => by
    replace hab := QuotientGroup.rightRel_apply.mp hab
    have hb : b = ((⟨b * a⁻¹, hab⟩ : M) : G) * a := by
      simp only [inv_mul_cancel_right]
    rw [hb, hinv]

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in
@[simp]
theorem leviQuotientLift_mk (M : Subgroup G) {β : Type*} (Θ : G → β)
    (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) (g : G) :
    leviQuotientLift M Θ hinv (leviQuotientMk M g) = Θ g :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] in
theorem measurable_leviQuotientLift (M : Subgroup G) {β : Type*} [MeasurableSpace β]
    (Θ : G → β) (hΘ : Measurable Θ) (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    Measurable (leviQuotientLift M Θ hinv) :=
  measurable_from_quotient.mpr hΘ

variable {M U V K : Subgroup G} [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology U] [SecondCountableTopology V]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant] [μM.IsMulRightInvariant]
  {μU : Measure U} [SFinite μU] [μU.IsMulLeftInvariant]
  {μV : Measure V} [SFinite μV] [μV.IsMulLeftInvariant]

/-- The image of `dk × dw` on `K × W` under `(k, w) ↦ M w k ∈ M \ G`. -/
def iwasawaPush (M : Subgroup G) (μ : Measure G) (K : Subgroup G) {W : Subgroup G}
    [MeasurableSpace W] (μW : Measure W) : Measure (LeviQuotient M) :=
  ((μ.restrict (K : Set G)).prod μW).map fun p : G × W => leviQuotientMk M ((p.2 : G) * p.1)

omit [MeasurableSpace M] [BorelSpace M] in
theorem measurable_iwasawaCoordinates {W : Subgroup G} [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] :
    Measurable fun p : G × W => leviQuotientMk M ((p.2 : G) * p.1) := by
  exact (measurable_leviQuotientMk M).comp
    ((continuous_subtype_val.measurable.comp measurable_snd).mul measurable_fst)

/-- **The two pushforwards to `M \ G` agree.** -/
theorem iwasawaPush_eq (hK : IsOpen (K : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hfacU : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hsplitU : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hfacV : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (hsplitV : ∀ (m : M) (v : V), (m : G) * v ∈ K ↔ (m : G) ∈ K ∧ (v : G) ∈ K)
    (hVK : μV {v : V | (v : G) ∈ K} = 1)
    (hMK : μM {m : M | (m : G) ∈ K} = 1) :
    iwasawaPush M μ K μV = iwasawaPush M μ K μU := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hV := measurable_iwasawaCoordinates (M := M) (W := V)
  have hU := measurable_iwasawaCoordinates (M := M) (W := U)
  rw [iwasawaPush, iwasawaPush, lintegral_map hf hV, lintegral_map hf hU,
    lintegral_prod (fun p : G × V => f (leviQuotientMk M ((p.2 : G) * p.1)))
      (hf.comp hV).aemeasurable,
    lintegral_prod (fun p : G × U => f (leviQuotientMk M ((p.2 : G) * p.1)))
      (hf.comp hU).aemeasurable]
  exact lintegral_exchange (μM := μM) hK hMU hfacU hsplitU hUK hMV hfacV hsplitV hVK hMK
    (fun g => f (leviQuotientMk M g)) (hf.comp (measurable_leviQuotientMk M))
    (fun m g => by simp only [leviQuotientMk_mul])

/-- **Exchange of opposite Iwasawa integrals, complex form.** Let `Θ : G → ℂ` be measurable and
invariant under left translation by `M`, with `(k, v) ↦ Θ(v k)` integrable on `K × V`. Then
`(k, u) ↦ Θ(u k)` is integrable on `K × U` and
`∫_K ∫_V Θ(v k) dv dk = ∫_K ∫_U Θ(u k) du dk`. -/
theorem integral_exchange (hK : IsOpen (K : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hfacU : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hsplitU : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hUK : μU {u : U | (u : G) ∈ K} = 1)
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hfacV : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (hsplitV : ∀ (m : M) (v : V), (m : G) * v ∈ K ↔ (m : G) ∈ K ∧ (v : G) ∈ K)
    (hVK : μV {v : V | (v : G) ∈ K} = 1)
    (hMK : μM {m : M | (m : G) ∈ K} = 1)
    (Θ : G → ℂ) (hΘ : Measurable Θ) (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g)
    (hint : Integrable (fun p : G × V => Θ ((p.2 : G) * p.1)) ((μ.restrict (K : Set G)).prod μV)) :
    Integrable (fun p : G × U => Θ ((p.2 : G) * p.1)) ((μ.restrict (K : Set G)).prod μU) ∧
      ∫ k in (K : Set G), ∫ v, Θ ((v : G) * k) ∂μV ∂μ =
        ∫ k in (K : Set G), ∫ u, Θ ((u : G) * k) ∂μU ∂μ := by
  have hpush := iwasawaPush_eq (μ := μ) (μM := μM) (μU := μU) (μV := μV) hK hMU hfacU hsplitU hUK
    hMV hfacV hsplitV hVK hMK
  have hV := measurable_iwasawaCoordinates (M := M) (W := V)
  have hU := measurable_iwasawaCoordinates (M := M) (W := U)
  have hL := measurable_leviQuotientLift M Θ hΘ hinv
  have hintV : Integrable (leviQuotientLift M Θ hinv) (iwasawaPush M μ K μV) :=
    (integrable_map_measure hL.aestronglyMeasurable hV.aemeasurable).mpr hint
  rw [hpush] at hintV
  have hintU : Integrable (fun p : G × U => Θ ((p.2 : G) * p.1))
      ((μ.restrict (K : Set G)).prod μU) :=
    (integrable_map_measure hL.aestronglyMeasurable hU.aemeasurable).mp hintV
  refine ⟨hintU, ?_⟩
  rw [← integral_prod _ hint, ← integral_prod _ hintU]
  have h1 := integral_map (μ := (μ.restrict (K : Set G)).prod μV) hV.aemeasurable
    hL.aestronglyMeasurable
  have h2 := integral_map (μ := (μ.restrict (K : Set G)).prod μU) hU.aemeasurable
    hL.aestronglyMeasurable
  change ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μV = _ at h1
  change ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μU = _ at h2
  rw [hpush] at h1
  exact h1.symm.trans h2

end Complex

section Integrability

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- A function invariant under right translation by an open subgroup is continuous. -/
theorem continuous_of_mul_right_invariant {β : Type*} [TopologicalSpace β] {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) (f : G → β) (hf : ∀ g : G, ∀ k ∈ K', f (g * k) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  have hnhds : (fun x => g⁻¹ * x) ⁻¹' (K' : Set G) ∈ 𝓝 g := by
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    show (K' : Set G) ∈ 𝓝 (g⁻¹ * g)
    rw [inv_mul_cancel]
    exact hK'.mem_nhds K'.one_mem
  refine tendsto_nhds_of_eventually_eq (Filter.mem_of_superset hnhds fun x hx => ?_)
  have := hf g (g⁻¹ * x) hx
  rwa [mul_inv_cancel_left] at this

variable {W K : Subgroup G} [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {μ : Measure G} [IsFiniteMeasureOnCompacts μ] {μW : Measure W} [SFinite μW]

omit [SecondCountableTopology G] in
/-- If `Θ` is invariant under right translation by an open subgroup and `w ↦ Θ(w k)` is
integrable for every `k ∈ K`, with `K` compact open, then `(k, w) ↦ Θ(w k)` is integrable on
`K × W`. -/
theorem integrable_iwasawaCoordinates {K' : Subgroup G} (hK' : IsOpen (K' : Set G))
    (hK : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (Θ : G → ℂ) (hright : ∀ g : G, ∀ k ∈ K', Θ (g * k) = Θ g)
    (hint : ∀ k ∈ K, Integrable (fun w : W => Θ ((w : G) * k)) μW) :
    Integrable (fun p : G × W => Θ ((p.2 : G) * p.1)) ((μ.restrict (K : Set G)).prod μW) := by
  have hc := continuous_of_mul_right_invariant hK' Θ hright
  have hmeas : AEStronglyMeasurable (fun p : G × W => Θ ((p.2 : G) * p.1))
      ((μ.restrict (K : Set G)).prod μW) :=
    (hc.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  refine ⟨ae_restrict_of_forall_mem hK.measurableSet fun k hk => hint k hk, ?_⟩
  have hcont : Continuous fun k : G => ∫ w, ‖Θ ((w : G) * k)‖ ∂μW := by
    refine continuous_of_mul_right_invariant hK' _ fun g k hk => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [← mul_assoc, hright _ k hk]
  exact hcont.continuousOn.integrableOn_compact' hKc hK.measurableSet

end Integrability

end Langlands.Plancherel.LeviInvariantIwasawaExchange
