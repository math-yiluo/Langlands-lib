import Langlands.Geometry.Analytic.TateAlgebra
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.RingTheory.MvPowerSeries.GaussNorm
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Set.Finite.Lemmas

/-! # The Gauss point of a strict Tate algebra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTateAlgebra

open Filter
open scoped Topology

section CoefficientNorm

variable {σ : Type u} {K : Type v} [NormedCommRing K] [IsUltrametricDist K]

/-- Restrictedness makes every positive coefficient superlevel set finite. -/
theorem finite_coeff_norm_ge (f : StrictTateAlgebra σ K) {ε : ℝ} (hε : 0 < ε) :
    {i : σ →₀ ℕ | ε ≤ ‖MvPowerSeries.coeff i (series σ K f)‖}.Finite := by
  have ht : Tendsto (fun i : σ →₀ ℕ => ‖MvPowerSeries.coeff i (series σ K f)‖)
      cofinite (𝓝 0) := by
    have hf := f.property
    change MvPowerSeries.IsRestricted (fun _ : σ => (1 : ℝ)) f.val at hf
    simpa [MvPowerSeries.IsRestricted, Finsupp.prod, series] using hf
  have he := ht.eventually (gt_mem_nhds hε)
  simpa only [Filter.eventually_cofinite, not_lt] using he

/-- The coefficient supremum is attained, including for the zero series. -/
theorem exists_norm_coeff_eq (f : StrictTateAlgebra σ K) :
    ∃ i : σ →₀ ℕ, ‖MvPowerSeries.coeff i (series σ K f)‖ = ‖f‖ := by
  classical
  by_cases hf : f = 0
  · refine ⟨0, ?_⟩
    subst f
    change ‖MvPowerSeries.coeff 0 (0 : MvPowerSeries σ K)‖ =
      ‖(0 : StrictTateAlgebra σ K)‖
    simp
  have hseries : series σ K f ≠ 0 := by
    intro h
    apply hf
    exact Subtype.ext h
  obtain ⟨j, hj⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero _).mp hseries
  let ε := ‖MvPowerSeries.coeff j (series σ K f)‖
  have hε : 0 < ε := norm_pos_iff.mpr hj
  let s := (finite_coeff_norm_ge f hε).toFinset
  have hjmem : j ∈ s := by simp [s, ε]
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image
    (fun k => ‖MvPowerSeries.coeff k (series σ K f)‖) ⟨j, hjmem⟩
  refine ⟨i, le_antisymm (norm_coeff_le σ K f i) ?_⟩
  apply (norm_le_iff σ K f (norm_nonneg _)).mpr
  intro k
  by_cases hk : k ∈ s
  · exact hmax k hk
  · have hsmall : ‖MvPowerSeries.coeff k (series σ K f)‖ < ε := by
      simpa [s, not_le] using hk
    exact hsmall.le.trans (hmax j hjmem)

/-- Choose the first maximal coefficient in a monomial order. -/
theorem exists_first_norm_coeff (m : MonomialOrder σ) (f : StrictTateAlgebra σ K) :
    ∃ i : σ →₀ ℕ, ‖MvPowerSeries.coeff i (series σ K f)‖ = ‖f‖ ∧
      ∀ k, m.toSyn k < m.toSyn i →
        ‖MvPowerSeries.coeff k (series σ K f)‖ < ‖f‖ := by
  obtain ⟨j, hj⟩ := exists_norm_coeff_eq f
  let s : Set m.syn := {a | ‖MvPowerSeries.coeff (m.toSyn.symm a) (series σ K f)‖ = ‖f‖}
  obtain ⟨a, ha, hmin⟩ := wellFounded_lt.has_min s ⟨m.toSyn j, by simpa [s] using hj⟩
  refine ⟨m.toSyn.symm a, ha, ?_⟩
  intro k hk
  apply lt_of_le_of_ne (norm_coeff_le σ K f k)
  intro he
  apply hmin (m.toSyn k) (by simpa [s] using he)
  simpa using hk

end CoefficientNorm

variable {σ : Type u} {K : Type v} [NormedField K] [IsUltrametricDist K]

/-- Multiplicativity is proved by the unique dominant convolution term. -/
theorem norm_mul_of_monomialOrder (m : MonomialOrder σ)
    (f g : StrictTateAlgebra σ K) : ‖f * g‖ = ‖f‖ * ‖g‖ := by
  classical
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨i, hi, hfirst⟩ := exists_first_norm_coeff m f
  obtain ⟨j, hj, hsecond⟩ := exists_first_norm_coeff m g
  have hdom : ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
      ‖MvPowerSeries.coeff p.1 (series σ K f) * MvPowerSeries.coeff p.2 (series σ K g)‖
        < ‖MvPowerSeries.coeff i (series σ K f)‖ *
          ‖MvPowerSeries.coeff j (series σ K g)‖ := by
    intro p hp hne
    have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
    have hsplit : m.toSyn p.1 < m.toSyn i ∨ m.toSyn p.2 < m.toSyn j := by
      by_contra! h
      have heq : m.toSyn p.1 + m.toSyn p.2 = m.toSyn i + m.toSyn j := by
        simpa using congrArg m.toSyn hsum
      have hp1 : m.toSyn p.1 = m.toSyn i := by
        apply le_antisymm _ h.1
        have hle : m.toSyn p.1 + m.toSyn j ≤ m.toSyn i + m.toSyn j := by
          calc
            m.toSyn p.1 + m.toSyn j ≤ m.toSyn p.1 + m.toSyn p.2 := by
              gcongr
              exact h.2
            _ = m.toSyn i + m.toSyn j := heq
        exact le_of_add_le_add_right hle
      have hp2 : m.toSyn p.2 = m.toSyn j := by
        simpa [hp1] using heq
      exact hne (Prod.ext (m.toSyn.injective hp1) (m.toSyn.injective hp2))
    rw [norm_mul, hi, hj]
    rcases hsplit with hp1 | hp2
    · exact (mul_le_mul_of_nonneg_left (norm_coeff_le σ K g _) (norm_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_right (hfirst _ hp1) (norm_pos_iff.mpr hg))
    · exact mul_lt_mul' (norm_coeff_le σ K f _) (hsecond _ hp2)
        (norm_nonneg _) (norm_pos_iff.mpr hf)
  have hc := MvPowerSeries.antidiagonal_dominant norm (series σ K f) (series σ K g)
    i j (fun a b => IsUltrametricDist.norm_add_le_max a b)
    (fun a b => norm_mul a b) (fun a => (norm_neg a).symm) hdom
  apply le_antisymm (norm_mul_le f g)
  calc
    ‖f‖ * ‖g‖ = ‖MvPowerSeries.coeff (i + j) (series σ K (f * g))‖ := by
      change _ = ‖MvPowerSeries.coeff (i + j) (series σ K f * series σ K g)‖
      rw [hc, norm_mul, hi, hj]
    _ ≤ ‖f * g‖ := norm_coeff_le σ K (f * g) _

/-- The coefficient norm itself is a spectrum point for finitely many variables. -/
def gaussPoint (n : ℕ) : BanachSpectrum (StrictTateAlgebra (Fin n) K) where
  toMulRingSeminorm :=
    { toFun := norm
      map_zero' := norm_zero
      map_one' := norm_one
      map_mul' := norm_mul_of_monomialOrder MonomialOrder.lex
      add_le' := norm_add_le
      neg' := norm_neg }
  le_norm _ := le_rfl

@[simp]
theorem gaussPoint_apply (n : ℕ) (f : StrictTateAlgebra (Fin n) K) :
    gaussPoint (K := K) n f = ‖f‖ := rfl

/-- On the actual Tate algebra the spectral unit ball equals the Gauss unit ball. -/
theorem forall_spectrum_le_one_iff (n : ℕ) (f : StrictTateAlgebra (Fin n) K) :
    (∀ x : BanachSpectrum (StrictTateAlgebra (Fin n) K), x f ≤ 1) ↔ ‖f‖ ≤ 1 :=
  ⟨fun h => h (gaussPoint n), fun h x => (x.le_norm f).trans h⟩

/-- The required power bound for the unquotiented strict Tate algebra. -/
theorem pow_bound_of_forall_spectrum_le_one (n : ℕ)
    (f : StrictTateAlgebra (Fin n) K)
    (hf : ∀ x : BanachSpectrum (StrictTateAlgebra (Fin n) K), x f ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, ‖f ^ r‖ ≤ C := by
  refine ⟨1, zero_lt_one, fun r => ?_⟩
  exact (norm_pow_le f r).trans
    (pow_le_one₀ (norm_nonneg f) ((forall_spectrum_le_one_iff n f).mp hf))

end Langlands.Analytic.StrictTateAlgebra
