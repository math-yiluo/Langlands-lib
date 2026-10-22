import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.CompletenessStatement

/-! # Completeness of positive-polyradius restricted power series -/

noncomputable section

open Filter Topology

universe u v

namespace Langlands.Analytic.GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v)
  [NormedCommRing K] [IsUltrametricDist K]

/-- An element is determined by its underlying formal series. -/
theorem series_injective : Function.Injective (series r K) :=
  fun _ _ h => Subtype.ext h

/-- Two elements with the same coefficients are equal. -/
theorem ext_coeff {f g : GeneralizedTateAlgebra r K}
    (h : ∀ d, MvPowerSeries.coeff d (series r K f) = MvPowerSeries.coeff d (series r K g)) :
    f = g :=
  series_injective r K (MvPowerSeries.ext h)

@[simp] theorem series_zero : series r K 0 = 0 := rfl

@[simp] theorem series_add (f g : GeneralizedTateAlgebra r K) :
    series r K (f + g) = series r K f + series r K g := rfl

@[simp] theorem series_neg (f : GeneralizedTateAlgebra r K) :
    series r K (-f) = -series r K f := rfl

@[simp] theorem series_sub (f g : GeneralizedTateAlgebra r K) :
    series r K (f - g) = series r K f - series r K g := rfl

@[simp] theorem series_smul (c : K) (f : GeneralizedTateAlgebra r K) :
    series r K (c • f) = c • series r K f := rfl

/-- A formal series with weighted cofinite decay, as an element of the algebra. -/
def ofSeries (F : MvPowerSeries σ K) (hF : MvPowerSeries.IsRestricted r F) :
    GeneralizedTateAlgebra r K :=
  ⟨F, hF⟩

@[simp] theorem series_ofSeries (F : MvPowerSeries σ K)
    (hF : MvPowerSeries.IsRestricted r F) : series r K (ofSeries r K F hF) = F := rfl

/-- The underlying series of every element has weighted cofinite decay. -/
theorem isRestricted_series (f : GeneralizedTateAlgebra r K) :
    MvPowerSeries.IsRestricted r (series r K f) :=
  f.property

/-- The coefficient of one fixed monomial, as a `K`-linear map. -/
def coeffLinearMap (d : σ →₀ ℕ) : GeneralizedTateAlgebra r K →ₗ[K] K where
  toFun f := MvPowerSeries.coeff d (series r K f)
  map_add' f g := map_add (MvPowerSeries.coeff d) (series r K f) (series r K g)
  map_smul' c f := (MvPowerSeries.coeff d).map_smul c (series r K f)

@[simp] theorem coeffLinearMap_apply (d : σ →₀ ℕ) (f : GeneralizedTateAlgebra r K) :
    coeffLinearMap r K d f = MvPowerSeries.coeff d (series r K f) := rfl

/-- Each coefficient is bounded by the norm divided by its positive weight. -/
theorem norm_coeff_le_div (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (series r K f)‖ ≤ ‖f‖ / r.weight d := by
  rw [le_div_iff₀ (r.weight_pos d)]
  exact weighted_norm_coeff_le r K f d

/-- The coefficient map at `d` is Lipschitz with constant the reciprocal weight. -/
theorem lipschitzWith_coeffLinearMap (d : σ →₀ ℕ) :
    LipschitzWith (Real.toNNReal (r.weight d)⁻¹) (coeffLinearMap r K d) := by
  apply AddMonoidHomClass.lipschitz_of_bound (coeffLinearMap r K d)
  intro f
  rw [coeffLinearMap_apply, inv_mul_eq_div]
  exact norm_coeff_le_div r K f d

theorem uniformContinuous_coeff (d : σ →₀ ℕ) :
    UniformContinuous fun f : GeneralizedTateAlgebra r K =>
      MvPowerSeries.coeff d (series r K f) :=
  (lipschitzWith_coeffLinearMap r K d).uniformContinuous

theorem continuous_coeff (d : σ →₀ ℕ) :
    Continuous fun f : GeneralizedTateAlgebra r K => MvPowerSeries.coeff d (series r K f) :=
  (uniformContinuous_coeff r K d).continuous

/-- Norm convergence implies convergence of every coefficient. -/
theorem tendsto_coeff_of_tendsto {ι : Type*} {l : Filter ι} {u : ι → GeneralizedTateAlgebra r K}
    {f : GeneralizedTateAlgebra r K} (hu : Tendsto u l (𝓝 f)) (d : σ →₀ ℕ) :
    Tendsto (fun i => MvPowerSeries.coeff d (series r K (u i))) l
      (𝓝 (MvPowerSeries.coeff d (series r K f))) :=
  ((continuous_coeff r K d).tendsto f).comp hu

/-- A Cauchy family in the algebra has Cauchy coefficients. -/
theorem cauchySeq_coeff {u : ℕ → GeneralizedTateAlgebra r K} (hu : CauchySeq u)
    (d : σ →₀ ℕ) : CauchySeq fun n => MvPowerSeries.coeff d (series r K (u n)) :=
  (uniformContinuous_coeff r K d).comp_cauchySeq hu

/-- A weighted coefficient bound against a family passes to its coefficientwise limit:
if `‖f - u i‖ ≤ ε` eventually and `u` converges coefficientwise to `F`, then every
weighted coefficient of `series f - F` is at most `ε`. -/
theorem weighted_norm_coeff_sub_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → GeneralizedTateAlgebra r K} {F : MvPowerSeries σ K}
    (hF : ∀ d, Tendsto (fun i => MvPowerSeries.coeff d (series r K (u i))) l
      (𝓝 (MvPowerSeries.coeff d F)))
    (f : GeneralizedTateAlgebra r K) {ε : ℝ} (hε : ∀ᶠ i in l, ‖f - u i‖ ≤ ε)
    (d : σ →₀ ℕ) :
    ‖MvPowerSeries.coeff d (series r K f - F)‖ * r.weight d ≤ ε := by
  have hlim : Tendsto
      (fun i => ‖MvPowerSeries.coeff d (series r K f - series r K (u i))‖ * r.weight d) l
      (𝓝 (‖MvPowerSeries.coeff d (series r K f - F)‖ * r.weight d)) := by
    simp only [map_sub]
    exact ((tendsto_const_nhds.sub (hF d)).norm).mul_const _
  refine le_of_tendsto hlim (hε.mono fun i hi => ?_)
  rw [← series_sub]
  exact (weighted_norm_coeff_le r K (f - u i) d).trans hi

/-- The coefficientwise limit of a Cauchy sequence has weighted cofinite decay. -/
theorem isRestricted_of_cauchySeq {u : ℕ → GeneralizedTateAlgebra r K} (hu : CauchySeq u)
    {F : MvPowerSeries σ K}
    (hF : ∀ d, Tendsto (fun n => MvPowerSeries.coeff d (series r K (u n))) atTop
      (𝓝 (MvPowerSeries.coeff d F))) :
    MvPowerSeries.IsRestricted r F := by
  rw [MvPowerSeries.IsRestricted, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  have hlate : ∀ d, ‖MvPowerSeries.coeff d (series r K (u N) - F)‖ * r.weight d ≤ ε / 2 :=
    weighted_norm_coeff_sub_le_of_tendsto r K hF (u N)
      (eventually_atTop.2 ⟨N, fun m hm => by
        rw [← dist_eq_norm]
        exact (hN N le_rfl m hm).le⟩)
  have hdecay := (Metric.tendsto_nhds.mp (isRestricted_series r K (u N))) (ε / 2) (half_pos hε)
  refine hdecay.mono fun d hd => ?_
  have hw := (r.weight_pos d).le
  change |‖MvPowerSeries.coeff d (series r K (u N))‖ * r.weight d - 0| < ε / 2 at hd
  change |‖MvPowerSeries.coeff d F‖ * r.weight d - 0| < ε
  rw [sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) hw)] at hd ⊢
  have htri : ‖MvPowerSeries.coeff d F‖ ≤ ‖MvPowerSeries.coeff d (series r K (u N))‖ +
      ‖MvPowerSeries.coeff d (series r K (u N) - F)‖ := by
    rw [map_sub, norm_sub_rev]
    exact norm_le_norm_add_norm_sub' _ _
  calc
    ‖MvPowerSeries.coeff d F‖ * r.weight d ≤
        ‖MvPowerSeries.coeff d (series r K (u N))‖ * r.weight d +
          ‖MvPowerSeries.coeff d (series r K (u N) - F)‖ * r.weight d := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right htri hw
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hd (hlate d)
    _ = ε := add_halves ε

/-- A Cauchy sequence converges in norm to the element formed from its coefficientwise
limit. -/
theorem tendsto_ofSeries_of_cauchySeq {u : ℕ → GeneralizedTateAlgebra r K} (hu : CauchySeq u)
    {F : MvPowerSeries σ K}
    (hF : ∀ d, Tendsto (fun n => MvPowerSeries.coeff d (series r K (u n))) atTop
      (𝓝 (MvPowerSeries.coeff d F))) :
    Tendsto u atTop (𝓝 (ofSeries r K F (isRestricted_of_cauchySeq r K hu hF))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  apply (norm_le_iff r K _ (half_pos hε).le).mpr
  intro d
  rw [series_sub, series_ofSeries]
  exact weighted_norm_coeff_sub_le_of_tendsto r K hF (u n)
    (eventually_atTop.2 ⟨N, fun m hm => by
      rw [← dist_eq_norm]
      exact (hN n hn m hm).le⟩) d

/-- Over complete coefficients, every Cauchy sequence has coefficientwise limits. -/
theorem exists_tendsto_coeff_of_cauchySeq [CompleteSpace K]
    {u : ℕ → GeneralizedTateAlgebra r K} (hu : CauchySeq u) :
    ∃ F : MvPowerSeries σ K, ∀ d, Tendsto
      (fun n => MvPowerSeries.coeff d (series r K (u n))) atTop
        (𝓝 (MvPowerSeries.coeff d F)) := by
  choose a ha using fun d => cauchySeq_tendsto_of_complete (cauchySeq_coeff r K hu d)
  exact ⟨a, ha⟩

/-- The weighted Gauss norm is complete over complete coefficients. -/
instance instCompleteSpace [CompleteSpace K] : CompleteSpace (GeneralizedTateAlgebra r K) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨F, hF⟩ := exists_tendsto_coeff_of_cauchySeq r K hu
  exact ⟨_, tendsto_ofSeries_of_cauchySeq r K hu hF⟩

/-- The published completeness target. -/
theorem completeness [CompleteSpace K] : CompletenessStatement r K :=
  instCompleteSpace r K

end Langlands.Analytic.GeneralizedTateAlgebra
