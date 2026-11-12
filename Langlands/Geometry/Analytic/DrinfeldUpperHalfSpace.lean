import Langlands.Geometry.Analytic.AnalyticAffineSpace
import Langlands.Geometry.Analytic.AtlasSubspaceRestriction

/-! # Drinfeld's upper half space -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Set Topology Metric PresentedAffinoidAlgebra GeneralizedTateAlgebra

namespace AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] (d : ℕ)

/-! ## Affine-linear functions -/

/-- The affine-linear function `c₀ + Σᵢ cᵢ₊₁ Tᵢ` in the `m`-th polydisc algebra. -/
def linearForm (m : ℕ) (c : Fin (d + 1) → K) : disc K d m :=
  algebraMap K (disc K d m) (c 0) + ∑ i : Fin d, c i.succ • coordinate K (disc K d m) i

/-- A series representative of `linearForm`. -/
def linearSeries (m : ℕ) (c : Fin (d + 1) → K) :
    GeneralizedTateAlgebra (disc K d m).polyradius K :=
  algebraMap K _ (c 0) + ∑ i : Fin d, c i.succ • X (disc K d m).polyradius K i

theorem presentationMap_linearSeries (m : ℕ) (c : Fin (d + 1) → K) :
    presentationMap K (disc K d m) (linearSeries K d m c) = linearForm K d m c := by
  change (presentationMap K (disc K d m)).toAlgHom (algebraMap K _ (c 0) +
    ∑ i : Fin d, c i.succ • X (disc K d m).polyradius K i) = _
  rw [map_add, AlgHom.commutes, map_sum]
  simp only [map_smul]
  rfl

theorem restriction_linearForm {m k : ℕ} (h : m ≤ k) (c : Fin (d + 1) → K) :
    restriction K d h (linearForm K d k c) = linearForm K d m c := by
  change (Polydisc.restriction (polyradius K d k) (polyradius K d m)
    (polyradius_le K d h)).toAlgHom (algebraMap K _ (c 0) +
      ∑ i : Fin d, c i.succ • coordinate K (disc K d k) i) = _
  rw [map_add, AlgHom.commutes, map_sum]
  simp only [map_smul]
  unfold linearForm
  congr 1

theorem linearForm_sub (m : ℕ) (a b : Fin (d + 1) → K) :
    linearForm K d m (a - b) = linearForm K d m a - linearForm K d m b := by
  simp only [linearForm, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]
  abel

theorem linearForm_smul (m : ℕ) (t : K) (a : Fin (d + 1) → K) :
    linearForm K d m (t • a) = algebraMap K (disc K d m) t * linearForm K d m a := by
  simp only [linearForm, Pi.smul_apply, smul_eq_mul, map_mul, mul_add, Finset.mul_sum,
    Algebra.smul_def, mul_assoc]

variable [CompleteSpace K]

theorem linearForm_glued {m k : ℕ} {s : BanachSpectrum (disc K d m)}
    {t : BanachSpectrum (disc K d k)} (h : (chartSystem K d).Glued m s k t)
    (c : Fin (d + 1) → K) : s (linearForm K d m c) = t (linearForm K d k c) := by
  obtain ⟨l, hlm, hlk, v, rfl, rfl⟩ := h
  change v (restriction K d hlm (linearForm K d m c)) =
    v (restriction K d hlk (linearForm K d k c))
  rw [restriction_linearForm, restriction_linearForm]

/-- The absolute value `|c₀ + Σᵢ cᵢ₊₁ Tᵢ|` at a point of the affine space. -/
def linearNorm (c : Fin (d + 1) → K) : Space K d → ℝ :=
  Quotient.lift (fun p => p.2 (linearForm K d p.1 c))
    (fun _ _ h => linearForm_glued K d h c)

@[simp]
theorem linearNorm_chart (c : Fin (d + 1) → K) (m : ℕ) (s : BanachSpectrum (disc K d m)) :
    linearNorm K d c (chart K d m s) = s (linearForm K d m c) := rfl

theorem continuous_linearNorm (c : Fin (d + 1) → K) : Continuous (linearNorm K d c) :=
  Continuous.quotient_lift (continuous_sigma fun m =>
    (BanachSpectrum.evaluation (linearForm K d m c)).continuous) _

omit [CompleteSpace K] in
/-- On the `m`-th polydisc, an affine-linear function with coefficients of norm
at most `B` has absolute value at most `(d + 1) B ‖ϖ‖⁻ᵐ`. -/
theorem linearForm_le (m : ℕ) (y : BanachSpectrum (disc K d m)) (c : Fin (d + 1) → K)
    {B : ℝ} (hB : 0 ≤ B) (hc : ∀ i, ‖c i‖ ≤ B) :
    y (linearForm K d m c) ≤ (d + 1) * B * radius K m := by
  have h1 := one_le_radius K m
  have hsum : y (∑ i : Fin d, c i.succ • coordinate K (disc K d m) i) ≤
      ∑ i : Fin d, B * radius K m := by
    refine (Finset.le_sum_of_subadditive (fun a => y a) (map_zero y.toMulRingSeminorm).le
      (fun a b => map_add_le_add y.toMulRingSeminorm a b) _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)
    change y (c i.succ • coordinate K (disc K d m) i) ≤ B * radius K m
    rw [Algebra.smul_def, map_mul y.toMulRingSeminorm]
    change y (algebraMap K (disc K d m) (c i.succ)) * y (coordinate K (disc K d m) i) ≤ _
    rw [BanachSpectrum.algebraMap_apply]
    exact mul_le_mul (hc _) ((y.le_norm _).trans (norm_coordinate_le K (disc K d m) i))
      (apply_nonneg y.toMulRingSeminorm _) hB
  calc y (linearForm K d m c)
      ≤ y (algebraMap K (disc K d m) (c 0)) +
          y (∑ i : Fin d, c i.succ • coordinate K (disc K d m) i) :=
        map_add_le_add y.toMulRingSeminorm _ _
    _ ≤ B * radius K m + ∑ i : Fin d, B * radius K m := by
        rw [BanachSpectrum.algebraMap_apply]
        refine add_le_add ?_ hsum
        calc ‖c 0‖ ≤ B := hc 0
          _ = B * 1 := (mul_one B).symm
          _ ≤ B * radius K m := mul_le_mul_of_nonneg_left h1 hB
    _ = (d + 1) * B * radius K m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end AnalyticAffineSpace

/-! ## The upper half space -/

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace

variable (F : Type v) [NontriviallyNormedField F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] (d : ℕ)

/-- The affine-linear function `a₀ + Σᵢ aᵢ₊₁ Tᵢ` with coefficients from `F`. -/
abbrev coefficients (a : Fin (d + 1) → F) : Fin (d + 1) → K := fun i => algebraMap F K (a i)

/-- Drinfeld's upper half space of dimension `d`: the points of the analytic
affine space at which no nonzero `F`-rational affine-linear function vanishes.
In homogeneous coordinates, these are the points of `ℙᵈ` off every
`F`-rational hyperplane (the hyperplane at infinity is one of them). -/
def Omega : Set (Space K d) :=
  {z | ∀ a : Fin (d + 1) → F, a ≠ 0 → linearNorm K d (coefficients F K d a) z ≠ 0}

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coefficients_sub (a b : Fin (d + 1) → F) :
    coefficients F K d (a - b) = coefficients F K d a - coefficients F K d b := by
  ext i
  simp [coefficients]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coefficients_smul (t : F) (a : Fin (d + 1) → F) :
    coefficients F K d (t • a) = algebraMap F K t • coefficients F K d a := by
  ext i
  simp [coefficients]

/-- The shell `{a | ‖c‖⁻¹ ≤ ‖a‖ ≤ 1}` of coefficient vectors. -/
def shell (c : F) : Set (Fin (d + 1) → F) := closedBall 0 1 \ ball 0 ‖c‖⁻¹

theorem isCompact_shell [ProperSpace F] (c : F) : IsCompact (shell F d c) :=
  (isCompact_closedBall 0 1).diff isOpen_ball

theorem ne_zero_of_mem_shell {c : F} (hc : 1 < ‖c‖) {a : Fin (d + 1) → F}
    (ha : a ∈ shell F d c) : a ≠ 0 := by
  rintro rfl
  exact ha.2 (mem_ball_self (inv_pos.2 (zero_lt_one.trans hc)))

theorem exists_smul_mem_shell {c : F} (hc : 1 < ‖c‖) {a : Fin (d + 1) → F} (ha : a ≠ 0) :
    ∃ t : F, t ≠ 0 ∧ t • a ∈ shell F d c := by
  obtain ⟨t, ht, h1, h2, -⟩ := rescale_to_shell hc one_pos ha
  refine ⟨t, ht, mem_closedBall_zero_iff.2 h1.le, fun hb => ?_⟩
  rw [mem_ball_zero_iff, ← one_div] at hb
  exact (lt_irrefl _) (hb.trans_le h2)

/-- The Laurent chart `{y | r ≤ |ℓ_c(y)|}` of the `M`-th polydisc. -/
def laurentChart (M : ℕ) (c : Fin (d + 1) → K) (r : ℝ) (hr : 0 < r) :
    RationalChart K (disc K d M) where
  arity := 1
  radii := ⟨fun _ => r⁻¹, fun _ => inv_pos.2 hr⟩
  denominator := linearSeries K d M c
  numerators := fun _ => 1
  generates := by
    apply Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self (0 : Fin 1))))
    show IsUnit (presentationMap K (disc K d M) 1)
    rw [map_one]
    exact isUnit_one

omit [CompleteSpace K] in
theorem mem_locus_laurentChart {M : ℕ} {c : Fin (d + 1) → K} {r : ℝ} {hr : 0 < r}
    {y : BanachSpectrum (disc K d M)} :
    y ∈ (laurentChart K d M c r hr).locus ↔ r ≤ y (linearForm K d M c) := by
  change (∀ _ : Fin 1, y (presentationMap K (disc K d M) 1) ≤
    r⁻¹ * y (presentationMap K (disc K d M) (linearSeries K d M c))) ↔ _
  rw [presentationMap_linearSeries, map_one]
  change (∀ _ : Fin 1, y.toMulRingSeminorm 1 ≤ _) ↔ _
  rw [map_one y.toMulRingSeminorm]
  constructor
  · intro h
    have h0 := h 0
    rwa [← div_eq_inv_mul, one_le_div₀ hr] at h0
  · intro h _
    rwa [← div_eq_inv_mul, one_le_div₀ hr]

/-- The intersection of the Laurent charts `{y | r ≤ |ℓ_c(y)|}` over a list of
coefficient vectors. -/
def laurentInter (M : ℕ) (r : ℝ) (hr : 0 < r) :
    List (Fin (d + 1) → K) → RationalChart K (disc K d M)
  | [] => RationalChart.whole K (disc K d M)
  | c :: L => (laurentChart K d M c r hr).inter (laurentInter M r hr L)

omit [CompleteSpace K] in
theorem mem_locus_laurentInter {M : ℕ} {r : ℝ} {hr : 0 < r} (L : List (Fin (d + 1) → K))
    {y : BanachSpectrum (disc K d M)} :
    y ∈ (laurentInter K d M r hr L).locus ↔ ∀ c ∈ L, r ≤ y (linearForm K d M c) := by
  induction L with
  | nil => simp [laurentInter, RationalChart.locus_whole]
  | cons c L ih =>
    rw [laurentInter, RationalChart.locus_inter, mem_inter_iff, mem_locus_laurentChart, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

variable [ProperSpace F]

/-- Every point of `Ω` has a rational domain of a closed polydisc as a
neighborhood inside `Ω`. -/
theorem exists_rational_nhds {z : Space K d} (hz : z ∈ Omega F K d) :
    ∃ (M : ℕ) (R : RationalChart K (disc K d M)),
      z ∈ chart K d M '' R.locus ∧ chart K d M '' R.locus ⊆ Omega F K d ∧
        chart K d M '' R.locus ∈ 𝓝 z := by
  obtain ⟨m, s, rfl⟩ := exists_chart K d z
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm F
  set M := m + 1
  set ρ := radius K M
  have hρ : 0 < ρ := radius_pos K M
  have hD : (0 : ℝ) < (d + 1) * ρ := mul_pos (by positivity) hρ
  -- the value of `|ℓ_a|` at the given point
  let f : (Fin (d + 1) → F) → ℝ := fun a =>
    linearNorm K d (coefficients F K d a) (chart K d m s)
  have hf_lip : ∀ a b, |f a - f b| ≤ (d + 1) * ‖a - b‖ * radius K m := by
    intro a b
    change |s (linearForm K d m _) - s (linearForm K d m _)| ≤ _
    refine (abs_sub_map_le_sub s.toMulRingSeminorm _ _).trans ?_
    rw [← linearForm_sub, ← coefficients_sub]
    refine linearForm_le K d m s _ (norm_nonneg _) fun i => ?_
    rw [coefficients, norm_algebraMap']
    exact norm_le_pi_norm (a - b) i
  have hf_cont : Continuous f := by
    refine LipschitzWith.continuous (K := ⟨(d + 1) * radius K m, by
      have := radius_pos K m; positivity⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, dist_eq_norm]
    calc |f a - f b| ≤ (d + 1) * ‖a - b‖ * radius K m := hf_lip a b
      _ = (d + 1) * radius K m * ‖a - b‖ := by ring
  have hf_pos : ∀ a ∈ shell F d c, 0 < f a := fun a ha =>
    lt_of_le_of_ne (apply_nonneg s.toMulRingSeminorm _)
      (hz a (ne_zero_of_mem_shell F d hc ha)).symm
  -- a positive lower bound on the compact shell
  have hne : (shell F d c).Nonempty := by
    obtain ⟨t, -, ht⟩ := exists_smul_mem_shell F d hc (a := Pi.single (0 : Fin (d + 1)) (1 : F))
      (fun h => by simpa using congrFun h (0 : Fin (d + 1)))
    exact ⟨_, ht⟩
  obtain ⟨a₀, ha₀, hmin⟩ := (isCompact_shell F d c).exists_isMinOn hne hf_cont.continuousOn
  set δ := f a₀
  have hδ : 0 < δ := hf_pos a₀ ha₀
  -- a finite net of the shell
  set η := δ / (2 * ((d + 1) * ρ))
  have hη : 0 < η := div_pos hδ (mul_pos two_pos hD)
  obtain ⟨T, hTS, hT, hcover⟩ := (isCompact_shell F d c).finite_cover_balls hη
  obtain ⟨T', rfl⟩ := hT.exists_finset_coe
  have hr : 0 < δ / 2 := half_pos hδ
  let L : List (Fin (d + 1) → K) := T'.toList.map (coefficients F K d)
  refine ⟨M, laurentInter K d M (δ / 2) hr L, ?_, ?_, ?_⟩
  · -- the point itself
    refine ⟨(chartSystem K d).pull (Nat.le_succ m) s, ?_, chart_pull K d _ s⟩
    rw [mem_locus_laurentInter]
    intro c' hc'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc'
    have hbT : b ∈ (T' : Set _) := Finset.mem_toList.1 hb
    have h1 : f b = (chartSystem K d).pull (Nat.le_succ m) s
        (linearForm K d M (coefficients F K d b)) :=
      (linearForm_glued K d ⟨m, le_refl m, Nat.le_succ m, s, (chartSystem K d).pull_refl m s,
        rfl⟩ _)
    rw [← h1]
    exact (half_le_self hδ.le).trans (hmin (hTS hbT))
  · -- the rational domain lies in `Ω`
    rintro _ ⟨y, hy, rfl⟩ a ha
    rw [mem_locus_laurentInter] at hy
    obtain ⟨t, ht0, hts⟩ := exists_smul_mem_shell F d hc ha
    obtain ⟨b, hbT, hb⟩ := mem_iUnion₂.1 (hcover hts)
    have hyb : δ / 2 ≤ y (linearForm K d M (coefficients F K d b)) :=
      hy _ (List.mem_map.2 ⟨b, Finset.mem_toList.2 hbT, rfl⟩)
    have hdiff : y (linearForm K d M (coefficients F K d (t • a - b))) < δ / 2 := by
      calc y (linearForm K d M (coefficients F K d (t • a - b)))
          ≤ (d + 1) * ‖t • a - b‖ * ρ := by
            refine linearForm_le K d M y _ (norm_nonneg _) fun i => ?_
            rw [coefficients, norm_algebraMap']
            exact norm_le_pi_norm (t • a - b) i
        _ < (d + 1) * η * ρ := by
            have : ‖t • a - b‖ < η := by rwa [← dist_eq_norm, ← mem_ball]
            have : (0 : ℝ) < d + 1 := by positivity
            gcongr
        _ = δ / 2 := by
            simp only [η]
            field_simp
    have hpos : 0 < y (linearForm K d M (coefficients F K d (t • a))) := by
      have htri := abs_sub_map_le_sub y.toMulRingSeminorm
        (linearForm K d M (coefficients F K d b))
        (linearForm K d M (coefficients F K d (t • a)))
      rw [← linearForm_sub, ← coefficients_sub, abs_le] at htri
      have h' : linearForm K d M (coefficients F K d (b - t • a)) =
          -linearForm K d M (coefficients F K d (t • a - b)) := by
        rw [coefficients_sub, coefficients_sub, linearForm_sub, linearForm_sub, neg_sub]
      have hneg : y (linearForm K d M (coefficients F K d (b - t • a))) =
          y (linearForm K d M (coefficients F K d (t • a - b))) := by
        rw [h']
        exact map_neg_eq_map y.toMulRingSeminorm _
      linarith [htri.2, hneg]
    rw [coefficients_smul, linearForm_smul, map_mul y.toMulRingSeminorm] at hpos
    change 0 < y (algebraMap K (disc K d M) (algebraMap F K t)) *
      y (linearForm K d M (coefficients F K d a)) at hpos
    rw [BanachSpectrum.algebraMap_apply] at hpos
    intro h0
    rw [linearNorm_chart] at h0
    rw [h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  · -- it is a neighborhood
    let V : Set (Space K d) := openDisc K d m ∩
      ⋂ b ∈ T', {w | δ / 2 < linearNorm K d (coefficients F K d b) w}
    have hV : IsOpen V :=
      (isOpen_openDisc K d m).inter (isOpen_biInter_finset fun b _ =>
        isOpen_lt continuous_const (continuous_linearNorm K d _))
    have hzV : chart K d m s ∈ V := by
      refine ⟨range_chart_subset_openDisc K d m ⟨s, rfl⟩, mem_iInter₂.2 fun b hb => ?_⟩
      exact (half_lt_self hδ).trans_le (hmin (hTS hb))
    refine Filter.mem_of_superset (hV.mem_nhds hzV) ?_
    rintro w ⟨hw, hwT⟩
    obtain ⟨y, rfl⟩ := openDisc_subset_range_chart K d m hw
    refine ⟨y, ?_, rfl⟩
    rw [mem_locus_laurentInter]
    intro c' hc'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc'
    exact (mem_iInter₂.1 hwT b (Finset.mem_toList.1 hb)).le

/-- `Ω` is an open subset of the affine space. -/
theorem isOpen_omega : IsOpen (Omega F K d) :=
  isOpen_iff_mem_nhds.2 fun _ hz =>
    let ⟨_, _, _, hRΩ, hRn⟩ := exists_rational_nhds F K d hz
    Filter.mem_of_superset hRn hRΩ

variable [NeZero d]

/-- `Ω` is covered locally by rational domains of the closed polydiscs contained
in it. -/
theorem isOriginalChartDomain :
    (rationalAtlas K d).IsOriginalChartDomain (Omega F K d) := by
  intro z
  obtain ⟨M, R, hzR, hRΩ, hRn⟩ := exists_rational_nhds F K d z.2
  refine ⟨{Subtype.val ⁻¹' (chart K d M '' R.locus)}, finite_singleton _, ?_, ?_, ?_⟩
  · rintro _ rfl
    refine ⟨chart K d M '' R.locus, ⟨DirectedRationalAtlas.Index.ofChart (atlas K d) M R, ?_⟩,
      hRΩ, rfl⟩
    exact DirectedRationalAtlas.atlas_ofChart_range (atlas K d) (atlas_hasDirectedCharts K d) M R
  · rintro _ rfl
    exact hzR
  · rw [sUnion_singleton]
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hRn

/-- The affinoid atlas of `Ω` whose charts are the rational domains of the
closed polydiscs contained in `Ω`. -/
def atlas : IndexedAffinoidAtlas.{u, u, u} K (Omega F K d) :=
  (rationalAtlas K d).subspaceAtlas (Omega F K d) (isOriginalChartDomain F K d)

/-- Drinfeld's upper half space as an atlas presentation. -/
def presentation : AffinoidAtlasPresentation.{u, u, u} K where
  space := TopCat.of (Omega F K d)
  atlas := atlas F K d

end DrinfeldUpperHalfSpace

end Langlands.Analytic
