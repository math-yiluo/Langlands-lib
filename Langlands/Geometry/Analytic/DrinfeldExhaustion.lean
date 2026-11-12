import Langlands.Geometry.Analytic.DrinfeldUpperHalfSpace

/-! # An exhaustion of Drinfeld's upper half space by rational domains -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology Metric PresentedAffinoidAlgebra GeneralizedTateAlgebra CategoryTheory

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable (F : Type v) [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ)

/-- A fixed scalar of norm greater than one; it fixes the shell of coefficient
vectors. -/
def bigScalar : F := (NormedField.exists_one_lt_norm F).choose

theorem one_lt_norm_bigScalar : 1 < ‖bigScalar F‖ :=
  (NormedField.exists_one_lt_norm F).choose_spec

/-- The thresholds `δ_N = 4⁻ᴺ`. -/
def threshold (N : ℕ) : ℝ := (4 : ℝ)⁻¹ ^ N

theorem threshold_pos (N : ℕ) : 0 < threshold N := by
  unfold threshold
  positivity

theorem threshold_succ (N : ℕ) : threshold (N + 1) = threshold N / 4 := by
  unfold threshold
  rw [pow_succ, div_eq_mul_inv]

/-- The mesh `η_N = δ_N / (2 (d + 1) ‖ϖ‖⁻ᴺ)`. -/
def mesh (N : ℕ) : ℝ := threshold N / (2 * ((d + 1) * radius K N))

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem mesh_pos (N : ℕ) : 0 < mesh K d N :=
  div_pos (threshold_pos N) (mul_pos two_pos (mul_pos (by positivity) (radius_pos K N)))

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem mesh_mul (N : ℕ) : (d + 1) * mesh K d N * radius K N = threshold N / 2 := by
  have h1 : (0 : ℝ) < d + 1 := by positivity
  have h2 := radius_pos K N
  unfold mesh
  field_simp

omit [CompleteSpace K] in
/-- Subtracting a nearby coefficient vector changes `|ℓ|` by at most
`(d + 1) ‖a - b‖ ‖ϖ‖⁻ᴹ`. -/
theorem linearForm_coefficients_ge (M : ℕ) (y : BanachSpectrum (disc K d M))
    (a b : Fin (d + 1) → F) :
    y (linearForm K d M (coefficients F K d b)) - (d + 1) * ‖a - b‖ * radius K M ≤
      y (linearForm K d M (coefficients F K d a)) := by
  have h : linearForm K d M (coefficients F K d b) =
      linearForm K d M (coefficients F K d a) +
        linearForm K d M (coefficients F K d (b - a)) := by
    rw [coefficients_sub, linearForm_sub]
    abel
  have h1 := map_add_le_add y.toMulRingSeminorm (linearForm K d M (coefficients F K d a))
    (linearForm K d M (coefficients F K d (b - a)))
  have h2 : y (linearForm K d M (coefficients F K d (b - a))) ≤
      (d + 1) * ‖a - b‖ * radius K M := by
    refine linearForm_le K d M y _ (norm_nonneg _) fun i => ?_
    rw [coefficients, norm_algebraMap', norm_sub_rev]
    exact norm_le_pi_norm (b - a) i
  rw [← h] at h1
  change y (linearForm K d M (coefficients F K d b)) ≤
    y (linearForm K d M (coefficients F K d a)) +
      y (linearForm K d M (coefficients F K d (b - a))) at h1
  linarith

omit [CompleteSpace K] in
/-- A point at which `|ℓ_{t • a}|` is positive for some `t ≠ 0` has `|ℓ_a| ≠ 0`. -/
theorem linearForm_ne_zero_of_smul {M : ℕ} (y : BanachSpectrum (disc K d M))
    {a : Fin (d + 1) → F} {t : F} (h : 0 < y (linearForm K d M (coefficients F K d (t • a)))) :
    y (linearForm K d M (coefficients F K d a)) ≠ 0 := by
  rw [coefficients_smul, linearForm_smul, map_mul y.toMulRingSeminorm] at h
  change 0 < y (algebraMap K (disc K d M) (algebraMap F K t)) *
    y (linearForm K d M (coefficients F K d a)) at h
  intro h0
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

variable [ProperSpace F]

omit [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K] in
theorem exists_net (N : ℕ) : ∃ T : Finset (Fin (d + 1) → F),
    (↑T : Set (Fin (d + 1) → F)) ⊆ shell F d (bigScalar F) ∧
      ∀ a ∈ shell F d (bigScalar F), ∃ b ∈ T, ‖a - b‖ < mesh K d N := by
  obtain ⟨T, hTS, hT, hcov⟩ :=
    (isCompact_shell F d (bigScalar F)).finite_cover_balls (mesh_pos K d N)
  obtain ⟨T', rfl⟩ := hT.exists_finset_coe
  refine ⟨T', hTS, fun a ha => ?_⟩
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.1 (hcov ha)
  exact ⟨b, hb, by rwa [← dist_eq_norm, ← mem_ball]⟩

/-- A chosen finite `η_N`-net of the shell. -/
def net (N : ℕ) : Finset (Fin (d + 1) → F) := (exists_net F K d N).choose

omit [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K] in
theorem net_subset_shell (N : ℕ) :
    (↑(net F K d N) : Set (Fin (d + 1) → F)) ⊆ shell F d (bigScalar F) :=
  (exists_net F K d N).choose_spec.1

omit [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K] in
theorem exists_mem_net (N : ℕ) {a : Fin (d + 1) → F} (ha : a ∈ shell F d (bigScalar F)) :
    ∃ b ∈ net F K d N, ‖a - b‖ < mesh K d N :=
  (exists_net F K d N).choose_spec.2 a ha

/-- The rational chart `{y ∈ E(0, ‖ϖ‖⁻ᴺ) | δ_N ≤ |ℓ_b(y)| for all b in the net}`. -/
def exhaustionChart (N : ℕ) : RationalChart K (disc K d N) :=
  laurentInter K d N (threshold N) (threshold_pos N)
    ((net F K d N).toList.map (coefficients F K d))

omit [CompleteSpace K] in
theorem mem_locus_exhaustionChart {N : ℕ} {y : BanachSpectrum (disc K d N)} :
    y ∈ (exhaustionChart F K d N).locus ↔
      ∀ b ∈ net F K d N, threshold N ≤ y (linearForm K d N (coefficients F K d b)) := by
  rw [exhaustionChart, mem_locus_laurentInter]
  constructor
  · intro h b hb
    exact h _ (List.mem_map.2 ⟨b, Finset.mem_toList.2 hb, rfl⟩)
  · intro h c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    exact h b (Finset.mem_toList.1 hb)

/-- The `N`-th member `V_N` of the exhaustion. -/
def exhaustion (N : ℕ) : Set (Space K d) :=
  chart K d N '' (exhaustionChart F K d N).locus

theorem exhaustion_subset_omega (N : ℕ) : exhaustion F K d N ⊆ Omega F K d := by
  rintro _ ⟨y, hy, rfl⟩ a ha
  rw [mem_locus_exhaustionChart] at hy
  obtain ⟨t, -, hts⟩ := exists_smul_mem_shell F d (one_lt_norm_bigScalar F) ha
  obtain ⟨b, hb, hab⟩ := exists_mem_net F K d N hts
  have h1 := linearForm_coefficients_ge F K d N y (t • a) b
  have h2 : (d + 1) * ‖t • a - b‖ * radius K N < threshold N / 2 := by
    rw [← mesh_mul K d N]
    have : (0 : ℝ) < d + 1 := by positivity
    have := radius_pos K N
    gcongr
  have hpos : 0 < y (linearForm K d N (coefficients F K d (t • a))) := by
    have := hy b hb
    have := threshold_pos N
    linarith
  rw [linearNorm_chart]
  exact linearForm_ne_zero_of_smul F K d y hpos

theorem exhaustion_mem_nhds {N : ℕ} {z : Space K d} (hz : z ∈ exhaustion F K d N) :
    exhaustion F K d (N + 1) ∈ 𝓝 z := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [mem_locus_exhaustionChart] at hy
  let V : Set (Space K d) := openDisc K d N ∩
    ⋂ b ∈ net F K d (N + 1), {w | threshold (N + 1) < linearNorm K d (coefficients F K d b) w}
  have hV : IsOpen V :=
    (isOpen_openDisc K d N).inter (isOpen_biInter_finset fun b _ =>
      isOpen_lt continuous_const (continuous_linearNorm K d _))
  have hzV : chart K d N y ∈ V := by
    refine ⟨range_chart_subset_openDisc K d N ⟨y, rfl⟩, mem_iInter₂.2 fun b hb => ?_⟩
    change threshold (N + 1) < y (linearForm K d N (coefficients F K d b))
    obtain ⟨b', hb', hbb'⟩ := exists_mem_net F K d N (net_subset_shell F K d (N + 1) hb)
    have h1 := linearForm_coefficients_ge F K d N y b b'
    have h2 : (d + 1) * ‖b - b'‖ * radius K N < threshold N / 2 := by
      rw [← mesh_mul K d N]
      have : (0 : ℝ) < d + 1 := by positivity
      have := radius_pos K N
      gcongr
    have h3 := hy b' hb'
    have h4 := threshold_pos N
    rw [threshold_succ]
    linarith
  refine Filter.mem_of_superset (hV.mem_nhds hzV) ?_
  rintro w ⟨hw, hwT⟩
  obtain ⟨y', rfl⟩ := openDisc_subset_range_chart K d N hw
  refine ⟨y', ?_, rfl⟩
  rw [mem_locus_exhaustionChart]
  intro b hb
  exact (mem_iInter₂.1 hwT b hb).le

theorem exhaustion_subset_succ (N : ℕ) : exhaustion F K d N ⊆ exhaustion F K d (N + 1) :=
  fun _ hz => mem_of_mem_nhds (exhaustion_mem_nhds F K d hz)

theorem exhaustion_mono {N N' : ℕ} (h : N ≤ N') : exhaustion F K d N ⊆ exhaustion F K d N' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (exhaustion_subset_succ F K d _)

theorem exhaustion_subset_interior (N : ℕ) :
    exhaustion F K d N ⊆ interior (exhaustion F K d (N + 1)) :=
  fun _ hz => mem_interior_iff_mem_nhds.2 (exhaustion_mem_nhds F K d hz)

theorem exists_mem_exhaustion {z : Space K d} (hz : z ∈ Omega F K d) :
    ∃ N, z ∈ exhaustion F K d N := by
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  set c := bigScalar F
  have hc := one_lt_norm_bigScalar F
  let f : (Fin (d + 1) → F) → ℝ := fun a =>
    linearNorm K d (coefficients F K d a) (chart K d m s)
  have hf_cont : Continuous f := by
    refine LipschitzWith.continuous (K := ⟨(d + 1) * radius K m, by
      have := radius_pos K m; positivity⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    have h1 := linearForm_coefficients_ge F K d m s a b
    have h2 := linearForm_coefficients_ge F K d m s b a
    rw [norm_sub_rev] at h2
    have h3 : ((d : ℝ) + 1) * ‖a - b‖ * radius K m = ((d : ℝ) + 1) * radius K m * ‖a - b‖ := by
      ring
    show |s (linearForm K d m _) - s (linearForm K d m _)| ≤
      ((d : ℝ) + 1) * radius K m * ‖a - b‖
    rw [abs_le]
    constructor <;> linarith
  have hne : (shell F d c).Nonempty := by
    obtain ⟨t, -, ht⟩ := exists_smul_mem_shell F d hc (a := Pi.single (0 : Fin (d + 1)) (1 : F))
      (fun h => by simpa using congrFun h (0 : Fin (d + 1)))
    exact ⟨_, ht⟩
  obtain ⟨a₀, ha₀, hmin⟩ := (isCompact_shell F d c).exists_isMinOn hne hf_cont.continuousOn
  have hδ : 0 < f a₀ :=
    lt_of_le_of_ne (apply_nonneg s.toMulRingSeminorm _)
      (hz a₀ (ne_zero_of_mem_shell F d hc ha₀)).symm
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (4 : ℝ)⁻¹ < 1)
  refine ⟨max m n, (chartSystem K d).pull (le_max_left m n) s, ?_, chart_pull K d _ s⟩
  rw [mem_locus_exhaustionChart]
  intro b hb
  have h1 : f b = (chartSystem K d).pull (le_max_left m n) s
      (linearForm K d (max m n) (coefficients F K d b)) :=
    linearForm_glued K d ⟨m, le_refl m, le_max_left m n, s, (chartSystem K d).pull_refl m s,
      rfl⟩ _
  rw [← h1]
  have hthr : threshold (max m n) ≤ (4 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right m n)
  exact (hthr.trans hn.le).trans (hmin (net_subset_shell F K d _ hb))

theorem iUnion_exhaustion : ⋃ N, exhaustion F K d N = Omega F K d :=
  subset_antisymm (iUnion_subset (exhaustion_subset_omega F K d))
    fun _ hz => mem_iUnion.2 (exists_mem_exhaustion F K d hz)

/-- Every compact subset of `Ω` lies in some member of the exhaustion. -/
theorem exists_subset_exhaustion {C : Set (Space K d)} (hC : IsCompact C)
    (hCΩ : C ⊆ Omega F K d) : ∃ N, C ⊆ exhaustion F K d N := by
  obtain ⟨N, hN⟩ := hC.elim_directed_cover (fun N => interior (exhaustion F K d N))
    (fun _ => isOpen_interior)
    (fun z hz => by
      obtain ⟨N, hN⟩ := exists_mem_exhaustion F K d (hCΩ hz)
      exact mem_iUnion.2 ⟨N + 1, exhaustion_subset_interior F K d N hN⟩)
    (Monotone.directed_le fun _ _ h => interior_mono (exhaustion_mono F K d h))
  exact ⟨N, hN.trans interior_subset⟩

/-! ## The exhaustion atlas -/

/-- The members of the exhaustion, as sets. -/
def ExhaustionIndex : Type u := {U : Set (Space K d) // ∃ N, exhaustion F K d N = U}

namespace ExhaustionIndex

variable {F K d}

/-- The first level at which a member occurs. -/
def level (U : ExhaustionIndex F K d) : ℕ := by
  classical
  exact Nat.find U.2

theorem exhaustion_level (U : ExhaustionIndex F K d) : exhaustion F K d U.level = U.1 := by
  classical
  exact Nat.find_spec U.2

/-- The member `V_N` as an index. -/
def ofLevel (N : ℕ) : ExhaustionIndex F K d := ⟨exhaustion F K d N, N, rfl⟩

end ExhaustionIndex

open ExhaustionIndex

theorem exhaustion_inter (N N' : ℕ) :
    exhaustion F K d N ∩ exhaustion F K d N' = exhaustion F K d (min N N') := by
  rcases le_total N N' with h | h
  · rw [min_eq_left h]
    exact inter_eq_left.2 (exhaustion_mono F K d h)
  · rw [min_eq_right h]
    exact inter_eq_right.2 (exhaustion_mono F K d h)

theorem exhaustion_subset_omega' (U : ExhaustionIndex F K d) : U.1 ⊆ Omega F K d :=
  U.exhaustion_level ▸ exhaustion_subset_omega F K d U.level

variable [NeZero d]

/-- `V_N` as a represented domain of the `N`-th closed polydisc. -/
def exhaustionDomain (N : ℕ) :
    IndexedAffinoidAtlas.DirectedDomain (AnalyticAffineSpace.atlas K d)
      (atlas_hasDirectedCharts K d) :=
  ⟨N, (exhaustionChart F K d N).toDomain⟩

theorem exhaustionDomain_locus (N : ℕ) :
    (exhaustionDomain F K d N).locus = exhaustion F K d N := rfl


/-- The chart of a member of the exhaustion, as a map into `Ω`. -/
def exhaustionChartMap (U : ExhaustionIndex F K d) :
    BanachSpectrum (exhaustionChart F K d U.level).algebra → Omega F K d :=
  fun x => ⟨(exhaustionDomain F K d U.level).ambientMap x,
    exhaustion_subset_omega F K d U.level (by
      have h := mem_range_self (f := (exhaustionDomain F K d U.level).ambientMap) x
      rw [(exhaustionDomain F K d U.level).range_ambientMap] at h
      exact h)⟩

theorem range_exhaustionChartMap (U : ExhaustionIndex F K d) :
    range (exhaustionChartMap F K d U) = Subtype.val ⁻¹' U.1 := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    have h := (exhaustionDomain F K d U.level).range_ambientMap ▸ mem_range_self x
    rw [exhaustionDomain_locus, U.exhaustion_level] at h
    exact h
  · intro hw
    have hw' : w.1 ∈ range (exhaustionDomain F K d U.level).ambientMap := by
      rw [(exhaustionDomain F K d U.level).range_ambientMap, exhaustionDomain_locus,
        U.exhaustion_level]
      exact hw
    obtain ⟨x, hx⟩ := hw'
    exact ⟨x, Subtype.ext hx⟩

theorem range_exhaustionChartMap_subset_iff {U V : ExhaustionIndex F K d} :
    range (exhaustionChartMap F K d U) ⊆ range (exhaustionChartMap F K d V) ↔
      U.1 ⊆ V.1 := by
  rw [range_exhaustionChartMap, range_exhaustionChartMap]
  constructor
  · intro h z hz
    exact h (show (⟨z, exhaustion_subset_omega' F K d U hz⟩ : Omega F K d) ∈
      Subtype.val ⁻¹' U.1 from hz)
  · intro h w hw
    exact h hw

theorem locus_subset_of_subset {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    (exhaustionDomain F K d U.level).locus ⊆ (exhaustionDomain F K d V.level).locus := by
  rw [exhaustionDomain_locus, exhaustionDomain_locus, U.exhaustion_level, V.exhaustion_level]
  exact h

/-- The restriction between two members of the exhaustion. -/
def exhaustionInclusion {U V : ExhaustionIndex F K d} (h : U.1 ⊆ V.1) :
    exhaustionDomain F K d U.level ⟶ exhaustionDomain F K d V.level :=
  IndexedAffinoidAtlas.DirectedDomain.Inclusion.ofSubset _ _ (locus_subset_of_subset F K d h)

theorem continuous_exhaustionChartMap (U : ExhaustionIndex F K d) :
    Continuous (exhaustionChartMap F K d U) :=
  (exhaustionDomain F K d U.level).ambientMap.continuous.subtype_mk _

theorem injective_exhaustionChartMap (U : ExhaustionIndex F K d) :
    Function.Injective (exhaustionChartMap F K d U) := by
  intro x x' h
  have h' := congrArg Subtype.val h
  exact (exhaustionDomain F K d U.level).domain.spectrumMap_injective
    ((isClosedEmbedding_chart K d U.level).injective h')

/-- The affinoid atlas of `Ω` given by the exhaustion `V_0 ⊆ V_1 ⊆ ⋯`. -/
def exhaustionAtlas : IndexedAffinoidAtlas.{u, u, u} K (Omega F K d) where
  Index := ExhaustionIndex F K d
  algebra U := (exhaustionChart F K d U.level).algebra
  chart := exhaustionChartMap F K d
  isEmbedding_chart U := ((continuous_exhaustionChartMap F K d U).isClosedEmbedding
    (injective_exhaustionChartMap F K d U)).isEmbedding
  chartDomain_injective := by
    intro U V h
    have h' : range (exhaustionChartMap F K d U) = range (exhaustionChartMap F K d V) := h
    exact Subtype.ext (subset_antisymm
      ((range_exhaustionChartMap_subset_iff F K d).1 h'.subset)
      ((range_exhaustionChartMap_subset_iff F K d).1 h'.symm.subset))
  locallyHausdorff _ := ⟨univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := by
    refine ⟨fun z => ?_, ?_⟩
    · obtain ⟨N, hN⟩ := exists_mem_exhaustion F K d z.2
      refine ⟨{range (exhaustionChartMap F K d (ofLevel (N + 1)))}, finite_singleton _,
        ?_, ?_, ?_⟩
      · rintro _ rfl
        exact ⟨_, rfl⟩
      · rintro _ rfl
        rw [range_exhaustionChartMap]
        exact exhaustion_subset_succ F K d N hN
      · rw [sUnion_singleton, range_exhaustionChartMap]
        exact continuous_subtype_val.continuousAt.preimage_mem_nhds
          (exhaustion_mem_nhds F K d hN)
    · rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩
      intro z
      let W : ExhaustionIndex F K d := ofLevel (min U.level V.level)
      have hW : range (exhaustionChartMap F K d W) =
          range (exhaustionChartMap F K d U) ∩ range (exhaustionChartMap F K d V) := by
        rw [range_exhaustionChartMap, range_exhaustionChartMap, range_exhaustionChartMap,
          ← preimage_inter, ← U.exhaustion_level, ← V.exhaustion_level, exhaustion_inter]
        rfl
      refine ⟨{univ}, finite_singleton _, ?_, ?_, ?_⟩
      · rintro _ rfl
        refine ⟨range (exhaustionChartMap F K d W), ⟨W, rfl⟩, hW.subset, ?_⟩
        ext w
        simp only [mem_univ, mem_preimage, true_iff]
        exact hW.symm.subset w.2
      · rintro _ rfl
        trivial
      · rw [sUnion_singleton]
        exact Filter.univ_mem
  restriction U V h := (exhaustionInclusion F K d
    ((range_exhaustionChartMap_subset_iff F K d).1 h)).restriction
  restriction_chart U V h x := Subtype.ext
    (IndexedAffinoidAtlas.DirectedDomain.Inclusion.ambientMap_naturality
      (exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 h)) x)
  restriction_universal U V h R φ hφ := by
    refine DirectedRationalAtlas.inclusion_universal (AnalyticAffineSpace.atlas K d)
      (atlas_hasDirectedCharts K d)
      (exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 h)) R φ ?_
    intro x
    obtain ⟨y, hy⟩ := hφ x
    have hmem : (exhaustionChartMap F K d V (BanachSpectrum.comap φ.toBoundedRingHom x)).1 ∈
        U.1 := by
      rw [← hy]
      have := mem_range_self (f := exhaustionChartMap F K d U) y
      rw [range_exhaustionChartMap] at this
      exact this
    rw [exhaustionDomain_locus, U.exhaustion_level]
    exact hmem
  restriction_id U h := by
    have : exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 h) =
        𝟙 (exhaustionDomain F K d U.level) :=
      @Subsingleton.elim (IndexedAffinoidAtlas.DirectedDomain.Inclusion _ _) _ _ _
    rw [this]
    rfl
  restriction_comp U V W hUV hVW hUW := by
    have : exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 hUW) =
        exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 hUV) ≫
          exhaustionInclusion F K d ((range_exhaustionChartMap_subset_iff F K d).1 hVW) :=
      @Subsingleton.elim (IndexedAffinoidAtlas.DirectedDomain.Inclusion _ _) _ _ _
    rw [this]
    rfl

/-- Drinfeld's upper half space with its exhaustion atlas. -/
def exhaustionPresentation : AffinoidAtlasPresentation.{u, u, u} K where
  space := TopCat.of (Omega F K d)
  atlas := exhaustionAtlas F K d

end DrinfeldUpperHalfSpace

end Langlands.Analytic
