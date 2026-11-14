import Langlands.Geometry.Analytic.PolynomialLocusCharts
import Langlands.Geometry.Analytic.AnalyticAffineSpace
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison

/-! # Gluing the bounded polynomial-locus charts -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra GeneralizedTateAlgebra AnalyticAffineSpace

namespace AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

omit [IsUltrametricDist K] in
/-- The cofinal radii used for the bounded polynomial loci. -/
theorem exists_radius_gt (r : ℝ) : ∃ m, r < radius K m :=
  pow_unbounded_of_one_lt r (one_lt_inv_norm_scale K)

/-- The actual weighted closed-kernel quotient at the `m`-th radius. -/
abbrev algebra (m : ℕ) : PresentedAffinoidAlgebra K :=
  PolynomialLocus.chart P (polyradius K P.arity m)

variable [CompleteSpace K]

/-- Restriction from the `k`-th to the `m`-th polydisc for `m ≤ k`. -/
def restriction {m k : ℕ} (h : m ≤ k) : BoundedAlgHom K (algebra K P k) (algebra K P m) :=
  PolynomialLocus.restriction P (polyradius K P.arity k) (polyradius K P.arity m) (polyradius_le K P.arity h)

theorem represents_restriction {m k : ℕ} (h : m ≤ k) :
    Represents K (restriction K P h)
      (Set.range (BanachSpectrum.comap (restriction K P h).toBoundedRingHom)) := by
  have h1 := PolynomialLocus.represents_restriction P (K := K) (polyradius K P.arity k) (polyradius K P.arity m)
    (polyradius_le K P.arity h)
  have h2 := PolynomialLocus.range_comap_restriction P (K := K) (polyradius K P.arity k) (polyradius K P.arity m)
    (polyradius_le K P.arity h)
  change Represents K (PolynomialLocus.restriction P _ _ _) (Set.range (BanachSpectrum.comap
    (PolynomialLocus.restriction P _ _ _).toBoundedRingHom))
  rw [h2]
  exact h1

/-- The chain of bounded polynomial loci `E(0, ‖ϖ‖⁻ᵐ)`, `m ∈ ℕ`, with the radius
restrictions as domain inclusions. -/
abbrev chartSystem : AffinoidChartSystem.{u, 0} K where
  Index := ℕ
  algebra := algebra K P
  Sub m k := m ≤ k
  restriction _ _ h := restriction K P h
  sub_refl := le_refl
  sub_trans := le_trans
  restriction_refl _ := PolynomialLocus.restriction_self P _
  restriction_trans _ _ := PolynomialLocus.restriction_trans P _ _ _ _ _
  represents _ _ h := represents_restriction K P h
  meet := by
    intro i j k hik hjk t hi hj
    rcases le_total i j with h | h
    · exact ⟨i, le_refl i, h, hi⟩
    · exact ⟨j, h, le_refl j, hj⟩

/-- The polynomial locus: the closed polydiscs glued along
the radius restrictions. -/
abbrev Space : Type u := (chartSystem K P).Space

/-- The spectrum chart of the `m`-th bounded polynomial locus. -/
def chart (m : ℕ) : BanachSpectrum (algebra K P m) → Space K P := (chartSystem K P).chart m

theorem pull_coordinate {m k : ℕ} (h : m ≤ k) (s : BanachSpectrum (algebra K P m)) (i : Fin P.arity) :
    (chartSystem K P).pull h s (coordinate K (algebra K P k) i) =
      s (coordinate K (algebra K P m) i) := by
  change s (PolynomialLocus.restriction P _ _ _ (coordinate K (PolynomialLocus.chart P _) i)) = _
  rw [PolynomialLocus.restriction_coordinate P]

theorem coordinate_glued {m k : ℕ} {s : BanachSpectrum (algebra K P m)}
    {t : BanachSpectrum (algebra K P k)} (h : (chartSystem K P).Glued m s k t) (i : Fin P.arity) :
    s (coordinate K (algebra K P m) i) = t (coordinate K (algebra K P k) i) := by
  obtain ⟨l, hlm, hlk, v, rfl, rfl⟩ := h
  exact (pull_coordinate K P hlm v i).trans (pull_coordinate K P hlk v i).symm

/-- The absolute value `|Tᵢ(x)|` of the `i`-th coordinate at a point of the
glued space. -/
def coordinateNorm (i : Fin P.arity) : Space K P → ℝ :=
  Quotient.lift (fun p => p.2 (coordinate K (algebra K P p.1) i))
    (fun _ _ h => coordinate_glued K P h i)

@[simp]
theorem coordinateNorm_chart (i : Fin P.arity) (m : ℕ) (s : BanachSpectrum (algebra K P m)) :
    coordinateNorm K P i (chart K P m s) = s (coordinate K (algebra K P m) i) := rfl

theorem continuous_coordinateNorm (i : Fin P.arity) : Continuous (coordinateNorm K P i) :=
  Continuous.quotient_lift (continuous_sigma fun m =>
    (BanachSpectrum.evaluation (coordinate K (algebra K P m) i)).continuous) _

theorem continuous_chart (m : ℕ) : Continuous (chart K P m) :=
  (chartSystem K P).continuous_chart m

theorem chart_pull {m k : ℕ} (h : m ≤ k) (s : BanachSpectrum (algebra K P m)) :
    chart K P k ((chartSystem K P).pull h s) = chart K P m s :=
  (chartSystem K P).chart_pull h s

theorem exists_chart (z : Space K P) : ∃ m s, chart K P m s = z :=
  (chartSystem K P).exists_chart z

/-- The `m`-th polydisc is exactly the set where all coordinate norms are at most
`‖ϖ‖⁻ᵐ`. -/
theorem mem_range_chart_iff (m : ℕ) (z : Space K P) :
    z ∈ range (chart K P m) ↔ ∀ i, coordinateNorm K P i z ≤ radius K m := by
  constructor
  · rintro ⟨s, rfl⟩ i
    rw [coordinateNorm_chart]
    exact (s.le_norm _).trans (norm_coordinate_le K (algebra K P m) i)
  · intro hz
    obtain ⟨k, s, rfl⟩ := exists_chart K P z
    rcases le_total k m with h | h
    · exact ⟨(chartSystem K P).pull h s, chart_pull K P h s⟩
    · have hs : s ∈ Set.range ((chartSystem K P).pull h) := by
        change s ∈ Set.range (BanachSpectrum.comap
          (PolynomialLocus.restriction P (polyradius K P.arity k) (polyradius K P.arity m)
            (polyradius_le K P.arity h)).toBoundedRingHom)
        rw [PolynomialLocus.range_comap_restriction P]
        exact hz
      obtain ⟨v, rfl⟩ := hs
      exact ⟨v, (chart_pull K P h v).symm⟩

theorem range_chart_mono {m k : ℕ} (h : m ≤ k) : range (chart K P m) ⊆ range (chart K P k) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, chart_pull K P h s⟩

/-- The open polydisc `D(0, ‖ϖ‖⁻⁽ᵐ⁺¹⁾)`. -/
def openDisc (m : ℕ) : Set (Space K P) :=
  {z | ∀ i, coordinateNorm K P i z < radius K (m + 1)}

theorem isOpen_openDisc (m : ℕ) : IsOpen (openDisc K P m) := by
  have h : openDisc K P m = ⋂ i, {z | coordinateNorm K P i z < radius K (m + 1)} := by
    ext z
    simp [openDisc]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_coordinateNorm K P i) continuous_const

theorem range_chart_subset_openDisc (m : ℕ) : range (chart K P m) ⊆ openDisc K P m :=
  fun z hz i => ((mem_range_chart_iff K P m z).1 hz i).trans_lt (radius_lt_radius_succ K m)

theorem openDisc_subset_range_chart (m : ℕ) : openDisc K P m ⊆ range (chart K P (m + 1)) :=
  fun z hz => (mem_range_chart_iff K P (m + 1) z).2 fun i => (hz i).le

theorem range_chart_mem_nhds {m : ℕ} {z : Space K P} (hz : z ∈ range (chart K P m)) :
    range (chart K P (m + 1)) ∈ 𝓝 z :=
  Filter.mem_of_superset ((isOpen_openDisc K P m).mem_nhds (range_chart_subset_openDisc K P m hz))
    (openDisc_subset_range_chart K P m)

theorem hasFiniteOverlaps : (chartSystem K P).HasFiniteOverlaps := by
  intro (i : ℕ) (j : ℕ)
  refine ⟨{⟨min i j, min_le_left i j, min_le_right i j⟩}, Set.finite_singleton _, ?_⟩
  rintro s t ⟨l, hli, hlj, v, hvs, hvt⟩
  refine ⟨_, rfl, (chartSystem K P).pull (le_min hli hlj : l ≤ min i j) v, ?_, ?_⟩
  · exact ((chartSystem K P).pull_trans (le_min hli hlj : l ≤ min i j)
      (min_le_left i j) v).symm.trans hvs
  · exact ((chartSystem K P).pull_trans (le_min hli hlj : l ≤ min i j)
      (min_le_right i j) v).symm.trans hvt

theorem isClosedEmbedding_chart (m : ℕ) : IsClosedEmbedding (chart K P m) :=
  (chartSystem K P).isClosedEmbedding_chart (hasFiniteOverlaps K P) m

theorem t2Space_range_chart (m : ℕ) : T2Space (range (chart K P m)) :=
  (isClosedEmbedding_chart K P m).isEmbedding.toHomeomorph.t2Space

/-- The glued polynomial locus is Hausdorff: two points lie in a common open
polydisc, which sits inside a closed polydisc chart. -/
instance : T2Space (Space K P) := by
  apply t2Space_of_separated_or_open_t2
  intro z z' _
  right
  obtain ⟨m, s, rfl⟩ := exists_chart K P z
  obtain ⟨k, t, rfl⟩ := exists_chart K P z'
  have hsub := openDisc_subset_range_chart K P (max m k)
  have := t2Space_range_chart K P (max m k + 1)
  refine ⟨openDisc K P (max m k), isOpen_openDisc K P _,
    range_chart_subset_openDisc K P _ (range_chart_mono K P (le_max_left m k) ⟨s, rfl⟩),
    range_chart_subset_openDisc K P _ (range_chart_mono K P (le_max_right m k) ⟨t, rfl⟩), ?_⟩
  exact T2Space.of_injective_continuous (f := Set.inclusion hsub)
    (Set.inclusion_injective hsub) (continuous_inclusion hsub)


end AffineAnalytification

end Langlands.Analytic
