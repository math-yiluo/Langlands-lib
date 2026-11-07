import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessStatement

/-!
# Finite-sum form of the Whittaker pairing

On a left coset space `N \ G`, a function that descends from `G`, is right
invariant under an open subgroup `K` and is supported in `N C` for a compact set
`C` takes only finitely many values on finitely many right `K`-orbits. Its
integral is therefore a finite sum `∑ c, m_c F(c)` with points `c` and weights
`m_c` depending only on `K`, `C` and the measure. This gives continuity of the
Whittaker pairing in parameters.
-/

noncomputable section

namespace Langlands.Whittaker.CompletenessPairing

open MeasureTheory QuotientIntegration

universe uG

section General

variable {G : Type uG} [Group G]

/-- The image in `N \ G` of the coset `g K`. -/
def orbit (N K : Subgroup G) (g : G) : Set (LeftQuotient N) :=
  Set.range fun k : K => (Quotient.mk _ (g * k.val) : LeftQuotient N)

theorem mk_mem_orbit (N K : Subgroup G) (g : G) :
    (Quotient.mk _ g : LeftQuotient N) ∈ orbit N K g :=
  ⟨1, by simp⟩

theorem orbit_eq_of_mk_mem {N K : Subgroup G} {g x : G}
    (hx : (Quotient.mk _ x : LeftQuotient N) ∈ orbit N K g) :
    orbit N K x = orbit N K g := by
  obtain ⟨k₀, hk₀⟩ := hx
  have hn : x * (g * k₀.val)⁻¹ ∈ N :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hk₀)
  have key : ∀ k : G, (Quotient.mk _ (x * k) : LeftQuotient N) =
      Quotient.mk _ (g * k₀.val * k) := by
    intro k
    refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
    simpa [mul_assoc] using N.inv_mem hn
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k₀ * k, by simp [key, mul_assoc]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k₀⁻¹ * k, ?_⟩
    simp [key, mul_assoc]

theorem disjoint_orbit {N K : Subgroup G} {a b : G} (h : orbit N K a ≠ orbit N K b) :
    Disjoint (orbit N K a) (orbit N K b) := by
  rw [Set.disjoint_left]
  intro y ha hb
  induction y using Quotient.inductionOn with
  | h x => exact h ((orbit_eq_of_mk_mem ha).symm.trans (orbit_eq_of_mk_mem hb))

theorem descend_eq_of_mem_orbit {N K : Subgroup G} {E : Type*} (F : G → E)
    (hF : ∀ h : N, ∀ g, F (h.val * g) = F g) (hK : ∀ g, ∀ k ∈ K, F (g * k) = F g)
    {g : G} {y : LeftQuotient N} (hy : y ∈ orbit N K g) : descend N F hF y = F g := by
  obtain ⟨k, rfl⟩ := hy
  exact hK g k.val k.property

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_orbit (N : Subgroup G) {K : Subgroup G} (hK : IsOpen (K : Set G)) (g : G) :
    IsOpen (orbit N K g) := by
  have : orbit N K g = leftQuotientMap N '' ((fun k => g * k) '' (K : Set G)) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨g * k.val, ⟨k.val, k.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  rw [this]
  exact (leftQuotient_isOpenQuotientMap N).isOpenMap _ (isOpenMap_mul_left g _ hK)

/-- The integral over `N \ G` of a descended function that is right invariant
under an open subgroup `K` and supported in `N C`, `C` compact, is a finite sum
`∑ c ∈ s, m c • F c` with `s` and `m` independent of the function. -/
theorem exists_integral_descend_eq_sum (N : Subgroup G)
    [MeasurableSpace (LeftQuotient N)] [OpensMeasurableSpace (LeftQuotient N)]
    (μ : Measure (LeftQuotient N)) [IsFiniteMeasureOnCompacts μ]
    {K : Subgroup G} (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    ∃ (s : Finset G) (m : G → ℝ), ∀ (F : G → ℂ) (hF : ∀ h : N, ∀ g, F (h.val * g) = F g),
      (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, F g ≠ 0 → ∃ n : N, ∃ c ∈ C, g = n.val * c) →
      ∫ q, descend N F hF q ∂μ = ∑ c ∈ s, m c • F c := by
  classical
  have hcomp : IsCompact (leftQuotientMap N '' C) :=
    hC.image (leftQuotient_isOpenQuotientMap N).continuous
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun c : C => orbit N K c.val)
    (fun c => isOpen_orbit N hK c.val) (by
      rintro _ ⟨c, hc, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, mk_mem_orbit N K c⟩)
  let t' : Finset G := t.map (Function.Embedding.subtype _)
  obtain ⟨s, hst, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (f := orbit N K) (t' : Set G) (t'.image (orbit N K)) (by
      intro S hS
      simpa using hS)
  -- every point of `N \ C` lies in the orbit of some point of `s`
  have hcov : ∀ c ∈ C, ∃ c' ∈ s, (Quotient.mk _ c : LeftQuotient N) ∈ orbit N K c' := by
    intro c hc
    obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.mp (ht ⟨c, hc, rfl⟩)
    have hmem : orbit N K i.val ∈ s.image (orbit N K) := by
      rw [himg]
      exact Finset.mem_image.mpr ⟨i.val, Finset.mem_map_of_mem _ hit, rfl⟩
    obtain ⟨c', hc's, hc'⟩ := Finset.mem_image.mp hmem
    exact ⟨c', hc's, hc' ▸ hi⟩
  refine ⟨s, fun c => μ.real (orbit N K c), ?_⟩
  intro F hF hFK hsupp
  have hpt : descend N F hF =
      fun q => ∑ c ∈ s, (orbit N K c).indicator (fun _ => F c) q := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      by_cases hq : ∃ c' ∈ s, (Quotient.mk _ g : LeftQuotient N) ∈ orbit N K c'
      · obtain ⟨c', hc's, hc'⟩ := hq
        rw [Finset.sum_eq_single c', Set.indicator_of_mem hc',
          descend_eq_of_mem_orbit F hF hFK hc']
        · intro b hb hbc
          apply Set.indicator_of_notMem
          intro hgb
          have hne : orbit N K b ≠ orbit N K c' := fun he => hbc (hinj hb hc's he)
          exact Set.disjoint_left.mp (disjoint_orbit hne) hgb hc'
        · intro h
          exact absurd hc's h
      · rw [Finset.sum_eq_zero]
        · change F g = 0
          by_contra hFg
          obtain ⟨n, c, hc, rfl⟩ := hsupp g hFg
          obtain ⟨c', hc's, hc'⟩ := hcov c hc
          refine hq ⟨c', hc's, ?_⟩
          have : (Quotient.mk _ (n.val * c) : LeftQuotient N) = Quotient.mk _ c :=
            Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))
          rw [this]
          exact hc'
        · intro c hc
          apply Set.indicator_of_notMem
          intro hgc
          exact hq ⟨c, hc, hgc⟩
  rw [hpt, integral_finsetSum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact integral_indicator_const _ (isOpen_orbit N hK c).measurableSet
  · intro c _
    by_cases h0 : F c = 0
    · simp [h0]
    · rw [integrable_indicator_iff (isOpen_orbit N hK c).measurableSet]
      have hsub : orbit N K c ⊆ leftQuotientMap N '' C := by
        rintro _ ⟨k, rfl⟩
        have hne : F (c * k.val) ≠ 0 := by rwa [hFK c k.val k.property]
        obtain ⟨n, c'', hc'', he⟩ := hsupp _ hne
        refine ⟨c'', hc'', ?_⟩
        show (Quotient.mk _ c'' : LeftQuotient N) = Quotient.mk _ (c * k.val)
        rw [he]
        exact (Quotient.sound (QuotientGroup.rightRel_apply.mpr (by simp))).symm
      exact integrableOn_const ((measure_mono hsub).trans_lt hcomp.measure_lt_top).ne

end General

section Whittaker

open HarmonicAnalysis RankinSelberg GeneralLinear Filter Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)] [OpensMeasurableSpace (LeftUnipotentQuotient n F)]

/-- For a fixed compact Whittaker test function `H` and an open subgroup `K`, the
pairing `f ↦ ∫ H f` on right `K`-invariant inverse-character functions is a finite
sum of values of `H f`. -/
theorem exists_integral_whittakerProductIntegrand_eq_sum (ψ : UnitaryAdditiveCharacter F)
    {H : WhittakerFunctions ψ n} (hH : IsCompactWhittakerTestFunction ψ n H)
    (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F)) :
    ∃ (s : Finset (Langlands.GeneralLinear (n + 1) F)) (m : Langlands.GeneralLinear (n + 1) F → ℝ),
      ∀ f : InverseWhittakerFunctions ψ n, (∀ g k, k ∈ K → f.val (g * k) = f.val g) →
        ∫ q, whittakerProductIntegrand ψ H f q ∂μ = ∑ c ∈ s, m c • (H.val c * f.val c) := by
  obtain ⟨⟨KH, hKH⟩, C, hC, hsupp⟩ := hH
  let K' : OpenSubgroup (Langlands.GeneralLinear (n + 1) F) := K ⊓ KH
  obtain ⟨s, m, hsm⟩ := exists_integral_descend_eq_sum (upperUnipotent (n + 1) F) μ
    (K := (K' : Subgroup _)) K'.isOpen hC
  refine ⟨s, m, fun f hf => ?_⟩
  refine hsm (fun g => H.val g * f.val g) _ ?_ ?_
  · intro g k hk
    have hk' : k ∈ K' := hk
    rw [hKH g k (OpenSubgroup.mem_inf.mp hk').2, hf g k (OpenSubgroup.mem_inf.mp hk').1]
  · intro g hg
    exact hsupp g (left_ne_zero_of_mul hg)

/-- Continuity of the Whittaker pairing: if inverse-character functions `f i`, all
right invariant under one open subgroup, converge pointwise to `f₀`, then their
pairings with a fixed compact Whittaker test function converge. -/
theorem tendsto_integral_whittakerProductIntegrand (ψ : UnitaryAdditiveCharacter F)
    {H : WhittakerFunctions ψ n} (hH : IsCompactWhittakerTestFunction ψ n H)
    (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]
    {ι : Type*} {l : Filter ι} (f : ι → InverseWhittakerFunctions ψ n)
    (f₀ : InverseWhittakerFunctions ψ n) (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hfK : ∀ i, ∀ g k, k ∈ K → (f i).val (g * k) = (f i).val g)
    (hf₀K : ∀ g k, k ∈ K → f₀.val (g * k) = f₀.val g)
    (hlim : ∀ g, Tendsto (fun i => (f i).val g) l (𝓝 (f₀.val g))) :
    Tendsto (fun i => ∫ q, whittakerProductIntegrand ψ H (f i) q ∂μ) l
      (𝓝 (∫ q, whittakerProductIntegrand ψ H f₀ q ∂μ)) := by
  obtain ⟨s, m, hsm⟩ := exists_integral_whittakerProductIntegrand_eq_sum ψ hH μ K
  simp_rw [hsm _ (hfK _), hsm f₀ hf₀K]
  exact tendsto_finsetSum _ fun c _ => ((hlim c).const_mul _).const_smul _

/-- If the pairings of `f i` with a fixed compact Whittaker test function vanish
eventually along a nontrivial filter, and the `f i` converge pointwise to `f₀`
within one space of right `K`-invariant functions, then the pairing with `f₀`
vanishes. -/
theorem integral_whittakerProductIntegrand_eq_zero_of_tendsto (ψ : UnitaryAdditiveCharacter F)
    {H : WhittakerFunctions ψ n} (hH : IsCompactWhittakerTestFunction ψ n H)
    (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]
    {ι : Type*} {l : Filter ι} [l.NeBot] (f : ι → InverseWhittakerFunctions ψ n)
    (f₀ : InverseWhittakerFunctions ψ n) (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hfK : ∀ i, ∀ g k, k ∈ K → (f i).val (g * k) = (f i).val g)
    (hf₀K : ∀ g k, k ∈ K → f₀.val (g * k) = f₀.val g)
    (hlim : ∀ g, Tendsto (fun i => (f i).val g) l (𝓝 (f₀.val g)))
    (hzero : ∀ᶠ i in l, ∫ q, whittakerProductIntegrand ψ H (f i) q ∂μ = 0) :
    ∫ q, whittakerProductIntegrand ψ H f₀ q ∂μ = 0 :=
  tendsto_nhds_unique (tendsto_integral_whittakerProductIntegrand ψ hH μ f f₀ K hfK hf₀K hlim)
    (tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm))

end Whittaker

end Langlands.Whittaker.CompletenessPairing
