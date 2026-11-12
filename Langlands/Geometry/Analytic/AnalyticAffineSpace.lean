import Langlands.Geometry.Analytic.PolydiscRestriction
import Langlands.Geometry.Analytic.AffinoidProductAtlas
import Langlands.Geometry.Analytic.DirectedRationalAtlas

/-! # The analytic affine space as an increasing union of closed polydiscs -/

noncomputable section

universe u

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra GeneralizedTateAlgebra

namespace AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K]

/-- A fixed element `ϖ` with `0 < ‖ϖ‖ < 1`; it fixes the radii of the
exhausting polydiscs. -/
def scale : K := (NormedField.exists_norm_lt_one K).choose

theorem norm_scale_pos : 0 < ‖scale K‖ := (NormedField.exists_norm_lt_one K).choose_spec.1

theorem norm_scale_lt_one : ‖scale K‖ < 1 := (NormedField.exists_norm_lt_one K).choose_spec.2

/-- The radius `‖ϖ‖⁻ᵐ` of the `m`-th polydisc. -/
def radius (m : ℕ) : ℝ := ‖scale K‖⁻¹ ^ m

theorem one_lt_inv_norm_scale : 1 < ‖scale K‖⁻¹ :=
  (one_lt_inv₀ (norm_scale_pos K)).2 (norm_scale_lt_one K)

theorem radius_pos (m : ℕ) : 0 < radius K m :=
  pow_pos (inv_pos.2 (norm_scale_pos K)) m

theorem radius_strictMono : StrictMono (radius K) :=
  pow_right_strictMono₀ (one_lt_inv_norm_scale K)

theorem radius_le_radius_iff {m k : ℕ} : radius K m ≤ radius K k ↔ m ≤ k :=
  (radius_strictMono K).le_iff_le

theorem radius_lt_radius_succ (m : ℕ) : radius K m < radius K (m + 1) :=
  radius_strictMono K (Nat.lt_succ_self m)

theorem one_le_radius (m : ℕ) : 1 ≤ radius K m :=
  one_le_pow₀ (one_lt_inv_norm_scale K).le

variable (d : ℕ)

/-- The constant polyradius `(‖ϖ‖⁻ᵐ, …, ‖ϖ‖⁻ᵐ)`. -/
def polyradius (m : ℕ) : PositivePolyradius (Fin d) :=
  ⟨fun _ => radius K m, fun _ => radius_pos K m⟩

theorem polyradius_le {m k : ℕ} (h : m ≤ k) (i : Fin d) :
    polyradius K d m i ≤ polyradius K d k i :=
  (radius_le_radius_iff K).2 h

variable [IsUltrametricDist K]

/-- The closed polydisc `E(0, ‖ϖ‖⁻ᵐ)` of dimension `d`. -/
abbrev disc (m : ℕ) : PresentedAffinoidAlgebra K :=
  polydisc K d (polyradius K d m)

variable [CompleteSpace K]

/-- Restriction from the `k`-th to the `m`-th polydisc for `m ≤ k`. -/
def restriction {m k : ℕ} (h : m ≤ k) : BoundedAlgHom K (disc K d k) (disc K d m) :=
  Polydisc.restriction (polyradius K d k) (polyradius K d m) (polyradius_le K d h)

theorem represents_restriction {m k : ℕ} (h : m ≤ k) :
    Represents K (restriction K d h)
      (Set.range (BanachSpectrum.comap (restriction K d h).toBoundedRingHom)) := by
  have h1 := Polydisc.represents_restriction (K := K) (polyradius K d k) (polyradius K d m)
    (polyradius_le K d h)
  have h2 := Polydisc.range_comap_restriction (K := K) (polyradius K d k) (polyradius K d m)
    (polyradius_le K d h)
  change Represents K (Polydisc.restriction _ _ _) (Set.range (BanachSpectrum.comap
    (Polydisc.restriction _ _ _).toBoundedRingHom))
  rw [h2]
  exact h1

/-- The chain of closed polydiscs `E(0, ‖ϖ‖⁻ᵐ)`, `m ∈ ℕ`, with the radius
restrictions as domain inclusions. -/
abbrev chartSystem : AffinoidChartSystem.{u, 0} K where
  Index := ℕ
  algebra := disc K d
  Sub m k := m ≤ k
  restriction _ _ h := restriction K d h
  sub_refl := le_refl
  sub_trans := le_trans
  restriction_refl _ := Polydisc.restriction_self _
  restriction_trans _ _ := Polydisc.restriction_trans _ _ _ _ _
  represents _ _ h := represents_restriction K d h
  meet := by
    intro i j k hik hjk t hi hj
    rcases le_total i j with h | h
    · exact ⟨i, le_refl i, h, hi⟩
    · exact ⟨j, h, le_refl j, hj⟩

/-- The analytic affine space of dimension `d`: the closed polydiscs glued along
the radius restrictions. -/
abbrev Space : Type u := (chartSystem K d).Space

/-- The chart of the `m`-th closed polydisc. -/
def chart (m : ℕ) : BanachSpectrum (disc K d m) → Space K d := (chartSystem K d).chart m

theorem pull_coordinate {m k : ℕ} (h : m ≤ k) (s : BanachSpectrum (disc K d m)) (i : Fin d) :
    (chartSystem K d).pull h s (coordinate K (disc K d k) i) =
      s (coordinate K (disc K d m) i) := by
  change s (Polydisc.restriction _ _ _ (coordinate K (polydisc K d _) i)) = _
  rw [Polydisc.restriction_coordinate]

theorem coordinate_glued {m k : ℕ} {s : BanachSpectrum (disc K d m)}
    {t : BanachSpectrum (disc K d k)} (h : (chartSystem K d).Glued m s k t) (i : Fin d) :
    s (coordinate K (disc K d m) i) = t (coordinate K (disc K d k) i) := by
  obtain ⟨l, hlm, hlk, v, rfl, rfl⟩ := h
  exact (pull_coordinate K d hlm v i).trans (pull_coordinate K d hlk v i).symm

/-- The absolute value `|Tᵢ(x)|` of the `i`-th coordinate at a point of the
glued space. -/
def coordinateNorm (i : Fin d) : Space K d → ℝ :=
  Quotient.lift (fun p => p.2 (coordinate K (disc K d p.1) i))
    (fun _ _ h => coordinate_glued K d h i)

@[simp]
theorem coordinateNorm_chart (i : Fin d) (m : ℕ) (s : BanachSpectrum (disc K d m)) :
    coordinateNorm K d i (chart K d m s) = s (coordinate K (disc K d m) i) := rfl

theorem continuous_coordinateNorm (i : Fin d) : Continuous (coordinateNorm K d i) :=
  Continuous.quotient_lift (continuous_sigma fun m =>
    (BanachSpectrum.evaluation (coordinate K (disc K d m) i)).continuous) _

theorem continuous_chart (m : ℕ) : Continuous (chart K d m) :=
  (chartSystem K d).continuous_chart m

theorem chart_pull {m k : ℕ} (h : m ≤ k) (s : BanachSpectrum (disc K d m)) :
    chart K d k ((chartSystem K d).pull h s) = chart K d m s :=
  (chartSystem K d).chart_pull h s

theorem exists_chart (z : Space K d) : ∃ m s, chart K d m s = z :=
  (chartSystem K d).exists_chart z

/-- The `m`-th polydisc is exactly the set where all coordinate norms are at most
`‖ϖ‖⁻ᵐ`. -/
theorem mem_range_chart_iff (m : ℕ) (z : Space K d) :
    z ∈ range (chart K d m) ↔ ∀ i, coordinateNorm K d i z ≤ radius K m := by
  constructor
  · rintro ⟨s, rfl⟩ i
    rw [coordinateNorm_chart]
    exact (s.le_norm _).trans (norm_coordinate_le K (disc K d m) i)
  · intro hz
    obtain ⟨k, s, rfl⟩ := exists_chart K d z
    rcases le_total k m with h | h
    · exact ⟨(chartSystem K d).pull h s, chart_pull K d h s⟩
    · have hs : s ∈ Set.range ((chartSystem K d).pull h) := by
        change s ∈ Set.range (BanachSpectrum.comap
          (Polydisc.restriction (polyradius K d k) (polyradius K d m)
            (polyradius_le K d h)).toBoundedRingHom)
        rw [Polydisc.range_comap_restriction]
        exact hz
      obtain ⟨v, rfl⟩ := hs
      exact ⟨v, (chart_pull K d h v).symm⟩

theorem range_chart_mono {m k : ℕ} (h : m ≤ k) : range (chart K d m) ⊆ range (chart K d k) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, chart_pull K d h s⟩

/-- The open polydisc `D(0, ‖ϖ‖⁻⁽ᵐ⁺¹⁾)`. -/
def openDisc (m : ℕ) : Set (Space K d) :=
  {z | ∀ i, coordinateNorm K d i z < radius K (m + 1)}

theorem isOpen_openDisc (m : ℕ) : IsOpen (openDisc K d m) := by
  have h : openDisc K d m = ⋂ i, {z | coordinateNorm K d i z < radius K (m + 1)} := by
    ext z
    simp [openDisc]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_coordinateNorm K d i) continuous_const

theorem range_chart_subset_openDisc (m : ℕ) : range (chart K d m) ⊆ openDisc K d m :=
  fun z hz i => ((mem_range_chart_iff K d m z).1 hz i).trans_lt (radius_lt_radius_succ K m)

theorem openDisc_subset_range_chart (m : ℕ) : openDisc K d m ⊆ range (chart K d (m + 1)) :=
  fun z hz => (mem_range_chart_iff K d (m + 1) z).2 fun i => (hz i).le

theorem range_chart_mem_nhds {m : ℕ} {z : Space K d} (hz : z ∈ range (chart K d m)) :
    range (chart K d (m + 1)) ∈ 𝓝 z :=
  Filter.mem_of_superset ((isOpen_openDisc K d m).mem_nhds (range_chart_subset_openDisc K d m hz))
    (openDisc_subset_range_chart K d m)

theorem hasFiniteOverlaps : (chartSystem K d).HasFiniteOverlaps := by
  intro (i : ℕ) (j : ℕ)
  refine ⟨{⟨min i j, min_le_left i j, min_le_right i j⟩}, Set.finite_singleton _, ?_⟩
  rintro s t ⟨l, hli, hlj, v, hvs, hvt⟩
  refine ⟨_, rfl, (chartSystem K d).pull (le_min hli hlj : l ≤ min i j) v, ?_, ?_⟩
  · exact ((chartSystem K d).pull_trans (le_min hli hlj : l ≤ min i j)
      (min_le_left i j) v).symm.trans hvs
  · exact ((chartSystem K d).pull_trans (le_min hli hlj : l ≤ min i j)
      (min_le_right i j) v).symm.trans hvt

theorem isClosedEmbedding_chart (m : ℕ) : IsClosedEmbedding (chart K d m) :=
  (chartSystem K d).isClosedEmbedding_chart (hasFiniteOverlaps K d) m

theorem t2Space_range_chart (m : ℕ) : T2Space (range (chart K d m)) :=
  (isClosedEmbedding_chart K d m).isEmbedding.toHomeomorph.t2Space

/-- The glued affine space is Hausdorff: two points lie in a common open
polydisc, which sits inside a closed polydisc chart. -/
instance : T2Space (Space K d) := by
  apply t2Space_of_separated_or_open_t2
  intro z z' _
  right
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  obtain ⟨k, t, rfl⟩ := exists_chart K d z'
  have hsub := openDisc_subset_range_chart K d (max m k)
  have := t2Space_range_chart K d (max m k + 1)
  refine ⟨openDisc K d (max m k), isOpen_openDisc K d _,
    range_chart_subset_openDisc K d _ (range_chart_mono K d (le_max_left m k) ⟨s, rfl⟩),
    range_chart_subset_openDisc K d _ (range_chart_mono K d (le_max_right m k) ⟨t, rfl⟩), ?_⟩
  exact T2Space.of_injective_continuous (f := Set.inclusion hsub)
    (Set.inclusion_injective hsub) (continuous_inclusion hsub)

section BasePoint

variable [NeZero d]

/-- The `K`-rational point `(ϖ⁻ᵐ, 0, …, 0)`, as a bounded evaluation of the
`m`-th polydisc algebra into `K`. -/
def basePointHom (m : ℕ) : BoundedAlgHom K (disc K d m) K := by
  letI := (disc K d m).ideal_closed
  exact BoundedAlgHom.liftQuotient K (disc K d m).ideal
    (evaluateHom (polyradius K d m) K K (fun i => if i = 0 then (scale K)⁻¹ ^ m else 0)
      ⟨1, one_pos, fun e => by
        rw [one_mul]
        refine monomialValue_norm_le_weight _ K norm_one.le _ (fun i => ?_) e
        split_ifs
        · rw [norm_pow, norm_inv]
          exact le_rfl
        · rw [norm_zero]
          exact (radius_pos K m).le⟩)
    (by
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0, map_zero])

theorem basePointHom_coordinate_zero (m : ℕ) :
    basePointHom K d m (coordinate K (disc K d m) (0 : Fin d)) = (scale K)⁻¹ ^ m := by
  change evaluate (polyradius K d m) K K (fun i => if i = 0 then (scale K)⁻¹ ^ m else 0)
    (X (polyradius K d m) K (0 : Fin d)) = _
  rw [evaluate_X, ite_eq_left_iff.2 (fun h => absurd rfl h)]

/-- The point of the `m`-th polydisc defined by `(ϖ⁻ᵐ, 0, …, 0)`. -/
def basePoint (m : ℕ) : BanachSpectrum (disc K d m) :=
  BanachSpectrum.comap (basePointHom K d m).toBoundedRingHom (BanachSpectrum.fieldPoint K)

theorem coordinateNorm_basePoint (m : ℕ) :
    coordinateNorm K d 0 (chart K d m (basePoint K d m)) = radius K m := by
  change ‖basePointHom K d m (coordinate K (disc K d m) (0 : Fin d))‖ = _
  rw [basePointHom_coordinate_zero, norm_pow, norm_inv]
  rfl

theorem range_chart_subset_iff {m k : ℕ} :
    range (chart K d m) ⊆ range (chart K d k) ↔ m ≤ k := by
  refine ⟨fun h => ?_, range_chart_mono K d⟩
  have hk := (mem_range_chart_iff K d k _).1 (h ⟨basePoint K d m, rfl⟩) 0
  rw [coordinateNorm_basePoint] at hk
  exact (radius_le_radius_iff K).1 hk

/-- The indexed affinoid atlas of the closed polydiscs `E(0, ‖ϖ‖⁻ᵐ)`. -/
def atlas : IndexedAffinoidAtlas.{u, u, 0} K (Space K d) where
  Index := ℕ
  algebra := disc K d
  chart := chart K d
  isEmbedding_chart m := (isClosedEmbedding_chart K d m).isEmbedding
  chartDomain_injective := by
    intro m k h
    have h' : range (chart K d m) = range (chart K d k) := h
    exact le_antisymm ((range_chart_subset_iff K d).1 h'.subset)
      ((range_chart_subset_iff K d).1 h'.symm.subset)
  locallyHausdorff _ := ⟨univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := by
    refine ⟨fun z => ?_, ?_⟩
    · obtain ⟨m, s, rfl⟩ := exists_chart K d z
      refine ⟨{range (chart K d (m + 1))}, Set.finite_singleton _, ?_, ?_, ?_⟩
      · rintro _ rfl
        exact ⟨m + 1, rfl⟩
      · rintro _ rfl
        exact range_chart_mono K d (Nat.le_succ m) ⟨s, rfl⟩
      · rw [Set.sUnion_singleton]
        exact range_chart_mem_nhds K d ⟨s, rfl⟩
    · rintro _ ⟨m, rfl⟩ _ ⟨k, rfl⟩
      intro z
      have hW : range (chart K d (min m k)) ⊆ range (chart K d m) ∩ range (chart K d k) :=
        subset_inter (range_chart_mono K d (min_le_left m k))
          (range_chart_mono K d (min_le_right m k))
      have hW' : range (chart K d m) ∩ range (chart K d k) ⊆ range (chart K d (min m k)) := by
        rcases le_total m k with h | h
        · rw [min_eq_left h]
          exact inter_subset_left
        · rw [min_eq_right h]
          exact inter_subset_right
      refine ⟨{univ}, Set.finite_singleton _, ?_, ?_, ?_⟩
      · rintro _ rfl
        refine ⟨range (chart K d (min m k)), ⟨min m k, rfl⟩, hW, ?_⟩
        ext w
        simp only [mem_univ, mem_preimage, true_iff]
        exact hW' w.2
      · rintro _ rfl
        trivial
      · rw [Set.sUnion_singleton]
        exact Filter.univ_mem
  restriction m k h := restriction K d ((range_chart_subset_iff K d).1 h)
  restriction_chart m k h x := chart_pull K d ((range_chart_subset_iff K d).1 h) x
  restriction_universal m k h R φ hφ := by
    apply (represents_restriction K d ((range_chart_subset_iff K d).1 h)).2.2 R φ
    intro x
    obtain ⟨s, hs⟩ := hφ x
    refine ⟨s, (isClosedEmbedding_chart K d k).injective ?_⟩
    exact (chart_pull K d ((range_chart_subset_iff K d).1 h) s).trans hs
  restriction_id m _ := Polydisc.restriction_self _
  restriction_comp _ _ _ _ _ _ := Polydisc.restriction_trans _ _ _ _ _

theorem atlas_hasDirectedCharts : (atlas K d).HasDirectedCharts := fun (m : ℕ) (k : ℕ) =>
  ⟨(max m k : ℕ), range_chart_mono K d (le_max_left m k), range_chart_mono K d (le_max_right m k)⟩

/-- The atlas presentation of the affine space by its closed polydiscs. -/
def presentation : AffinoidAtlasPresentation.{u, u, 0} K where
  space := TopCat.of (Space K d)
  atlas := atlas K d

/-- The rational enlargement of the polydisc atlas: its charts are all rational
domains of all the closed polydiscs. -/
def rationalAtlas : IndexedAffinoidAtlas.{u, u, u} K (Space K d) :=
  DirectedRationalAtlas.atlas (atlas K d) (atlas_hasDirectedCharts K d)

/-- The atlas presentation of the affine space by the rational domains of its
closed polydiscs. -/
def rationalPresentation : AffinoidAtlasPresentation.{u, u, u} K where
  space := TopCat.of (Space K d)
  atlas := rationalAtlas K d

end BasePoint

end AnalyticAffineSpace

end Langlands.Analytic
