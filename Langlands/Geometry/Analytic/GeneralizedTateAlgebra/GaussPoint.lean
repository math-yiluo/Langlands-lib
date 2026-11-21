import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Definitions
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Data.Finsupp.MonomialOrder

/-! # The Gauss point of a generalized Tate algebra -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Filter
open scoped Topology

theorem PositivePolyradius.weight_add {σ : Type u} (r : PositivePolyradius σ)
    (a b : σ →₀ ℕ) : r.weight (a + b) = r.weight a * r.weight b := by
  classical
  simp [PositivePolyradius.weight, Finsupp.prod_add_index', pow_add]

namespace GeneralizedTateAlgebra

variable {σ : Type u} {r : PositivePolyradius σ} {K : Type v} [NormedField K] [IsUltrametricDist K]

private def weightedCoeff (f : GeneralizedTateAlgebra r K) (i : σ →₀ ℕ) : ℝ :=
  ‖MvPowerSeries.coeff i (series r K f)‖ * r.weight i

private theorem finite_weightedCoeff_ge (f : GeneralizedTateAlgebra r K) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ weightedCoeff f i}.Finite := by
  have ht : Tendsto (weightedCoeff f) cofinite (𝓝 0) := f.property
  have he := ht.eventually (gt_mem_nhds hε)
  simpa only [Filter.eventually_cofinite, not_lt] using he

private theorem exists_weightedCoeff_eq (f : GeneralizedTateAlgebra r K) :
    ∃ i, weightedCoeff f i = ‖f‖ := by
  classical
  by_cases hf : f = 0
  · subst f
    exact ⟨0, by simp [weightedCoeff, series]; rfl⟩
  have hseries : series r K f ≠ 0 := fun h => hf (Subtype.ext h)
  obtain ⟨j, hj⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _).mp hseries
  let ε := weightedCoeff f j
  have hε : 0 < ε := mul_pos (norm_pos_iff.mpr hj) (r.weight_pos j)
  let s := (finite_weightedCoeff_ge f hε).toFinset
  have hjmem : j ∈ s := by simp [s, ε]
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (weightedCoeff f) ⟨j, hjmem⟩
  refine ⟨i, le_antisymm (weighted_norm_coeff_le r K f i) ?_⟩
  apply (norm_le_iff r K f (mul_nonneg (norm_nonneg _) (r.weight_pos i).le)).mpr
  intro k
  by_cases hk : k ∈ s
  · exact hmax k hk
  · have : weightedCoeff f k < ε := by simpa [s, not_le] using hk
    exact this.le.trans (hmax j hjmem)

private theorem exists_first_weightedCoeff (m : MonomialOrder σ) (f : GeneralizedTateAlgebra r K) :
    ∃ i, weightedCoeff f i = ‖f‖ ∧
      ∀ j, m.toSyn j < m.toSyn i → weightedCoeff f j < ‖f‖ := by
  obtain ⟨j, hj⟩ := exists_weightedCoeff_eq f
  let s : Set m.syn := {a | weightedCoeff f (m.toSyn.symm a) = ‖f‖}
  obtain ⟨a, ha, hmin⟩ := wellFounded_lt.has_min s ⟨m.toSyn j, by simp [s, hj]⟩
  refine ⟨m.toSyn.symm a, ha, fun k hk => ?_⟩
  refine lt_of_le_of_ne (show weightedCoeff f k ≤ ‖f‖ from weighted_norm_coeff_le r K f k) ?_
  exact fun heq => hmin (m.toSyn k) (by simpa [s] using heq) (by simpa using hk)

/-- The weighted Gauss norm is multiplicative (the first pair of maximal coefficients
in the monomial order gives the unique dominant term in its convolution coefficient). -/
theorem gauss_norm_mul (m : MonomialOrder σ) (f g : GeneralizedTateAlgebra r K) :
    ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨i, hi, hfi⟩ := exists_first_weightedCoeff m f
  obtain ⟨j, hj, hgj⟩ := exists_first_weightedCoeff m g
  apply le_antisymm (norm_mul_le f g)
  refine MvPowerSeries.gaussNorm_le_mul norm r (series r K f) (series r K g) norm_mul
    IsUltrametricDist.norm_add_le_max (fun a => (norm_neg a).symm)
    (hasGaussNorm r K (f * g)) ⟨i, j, hi, hj, ?_⟩
  intro p hp hne
  have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.1 hp
  have hlt : m.toSyn p.1 < m.toSyn i ∨ m.toSyn p.2 < m.toSyn j := by
    by_contra! h
    have heq : m.toSyn p.1 + m.toSyn p.2 = m.toSyn i + m.toSyn j := by
      simpa using congrArg m.toSyn hsum
    have hpi : m.toSyn p.1 = m.toSyn i := by
      apply le_antisymm _ h.1
      have hle : m.toSyn p.1 + m.toSyn j ≤ m.toSyn i + m.toSyn j := calc
        _ ≤ m.toSyn p.1 + m.toSyn p.2 := by
          gcongr
          exact h.2
        _ = _ := heq
      exact le_of_add_le_add_right hle
    have hpj : m.toSyn p.2 = m.toSyn j := by simpa [hpi] using heq
    exact hne (Prod.ext (m.toSyn.injective hpi) (m.toSyn.injective hpj))
  have hdom : weightedCoeff f p.1 * weightedCoeff g p.2 < weightedCoeff f i * weightedCoeff g j := by
    rw [hi, hj]
    rcases hlt with h | h
    · exact (mul_le_mul_of_nonneg_left (weighted_norm_coeff_le r K g p.2)
        (mul_nonneg (norm_nonneg _) (r.weight_pos p.1).le)).trans_lt
        (mul_lt_mul_of_pos_right (hfi _ h) (norm_pos_iff.2 hg))
    · exact mul_lt_mul' (weighted_norm_coeff_le r K f p.1) (hgj _ h)
        (mul_nonneg (norm_nonneg _) (r.weight_pos p.2).le) (norm_pos_iff.2 hf)
  refine lt_of_mul_lt_mul_right ?_ (r.weight_pos (i + j)).le
  calc ‖MvPowerSeries.coeff p.1 (series r K f) * MvPowerSeries.coeff p.2 (series r K g)‖ *
      r.weight (i + j) = weightedCoeff f p.1 * weightedCoeff g p.2 := by
        rw [← hsum, r.weight_add, norm_mul, weightedCoeff, weightedCoeff]
        ring
    _ < weightedCoeff f i * weightedCoeff g j := hdom
    _ = ‖MvPowerSeries.coeff i (series r K f)‖ * ‖MvPowerSeries.coeff j (series r K g)‖ *
      r.weight (i + j) := by
        rw [r.weight_add, weightedCoeff, weightedCoeff]
        ring

/-- The Gauss point with arbitrary positive real polyradius in finitely many variables. -/
def gaussPoint {n : ℕ} (r : PositivePolyradius (Fin n)) (K : Type v) [NormedField K]
    [IsUltrametricDist K] : BanachSpectrum (GeneralizedTateAlgebra r K) where
  toMulRingSeminorm :=
    { toFun := norm
      map_zero' := norm_zero
      map_one' := norm_one
      map_mul' := gauss_norm_mul MonomialOrder.lex
      add_le' := norm_add_le
      neg' := norm_neg }
  le_norm _ := le_rfl

@[simp] theorem gaussPoint_apply {n : ℕ} (r : PositivePolyradius (Fin n)) (K : Type v)
    [NormedField K] [IsUltrametricDist K] (f : GeneralizedTateAlgebra r K) :
    gaussPoint r K f = ‖f‖ := rfl

/-- The weighted norm of a sum with distinct monomial exponents is bounded by `B`
exactly when each weighted coefficient is bounded by `B`. -/
theorem norm_sum_monomial_le_iff {ι : Type w} [Fintype ι] (e : ι → σ →₀ ℕ)
    (he : Function.Injective e) (c : ι → K) {B : ℝ} (hB : 0 ≤ B) :
    ‖∑ i, monomial r K (e i) (c i)‖ ≤ B ↔ ∀ i, ‖c i‖ * r.weight (e i) ≤ B := by
  classical
  have hcoeff (d : σ →₀ ℕ) :
      MvPowerSeries.coeff d (series r K (∑ i, monomial r K (e i) (c i))) =
      ∑ i, if e i = d then c i else 0 := by
    let φ : GeneralizedTateAlgebra r K →ₐ[K] MvPowerSeries σ K :=
      (weightedRestrictedSubalgebra r K).val
    let ψ : GeneralizedTateAlgebra r K →+ K :=
      (MvPowerSeries.coeff d).toAddMonoidHom.comp φ.toAddMonoidHom
    change ψ (∑ i, monomial r K (e i) (c i)) = _
    rw [map_sum ψ]
    exact Finset.sum_congr rfl fun i _ => coeff_monomial r K (e i) d (c i)
  have hsingle (i : ι) : (∑ j, if e j = e i then c j else 0) = c i := by
    simp only [he.eq_iff]
    simp
  rw [norm_le_iff r K _ hB]
  simp only [hcoeff]
  constructor
  · intro h i
    simpa only [hsingle] using h (e i)
  · intro h d
    by_cases hd : d ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hd
      simpa only [hsingle] using h i
    · have hne (i : ι) : e i ≠ d := fun hi => hd ⟨i, hi⟩
      simp [hne, hB]

end GeneralizedTateAlgebra

end Langlands.Analytic
