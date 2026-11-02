import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentGaussContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Finite rational decomposition of weighted Laurent inequalities -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- A finite family of ratios with an explicit positive denominator lower bound. -/
def boundedRatios {I : Type v} [Fintype I] (b : A) (q : ℝ) (hq : 0 < q)
    (a : I → A) (r : I → ℝ) (hr : ∀ i, 0 < r i) : RationalChart K A := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine {
    arity := Fintype.card I + 1
    radii := ⟨Fin.cons q⁻¹ (fun j => r (e j)), fun j =>
      Fin.cases (inv_pos.mpr hq) (fun j => hr (e j)) j⟩
    denominator := coefficientRepresentative A b
    numerators := Fin.cons 1 (fun j => coefficientRepresentative A (a (e j)))
    generates := ?_ }
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  right
  exact ⟨0, by simp only [Fin.cons_zero, map_one]⟩

@[simp] theorem mem_locus_boundedRatios {I : Type v} [Fintype I]
    (b : A) (q : ℝ) (hq : 0 < q)
    (a : I → A) (r : I → ℝ) (hr : ∀ i, 0 < r i) (x : BanachSpectrum A) :
    x ∈ (boundedRatios b q hq a r hr).locus ↔
      q ≤ x b ∧ ∀ i, x (a i) ≤ r i * x b := by
  classical
  simp only [boundedRatios, locus, RationalPresentation.locus,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    presentationMap_coefficientRepresentative, map_one]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨?_, fun i => ?_⟩
    · rwa [← div_eq_inv_mul, le_div_iff₀ hq, one_mul] at h0
    · simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin I) i)
  · rintro ⟨h0, h⟩
    refine ⟨?_, fun j => h _⟩
    rwa [← div_eq_inv_mul, le_div_iff₀ hq, one_mul]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)] {A : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem coe_weightedCoefficient (x : BanachSpectrum A)
    (p : AddMonoidAlgebra A ℤ) (n : ℤ) :
    ((Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n : NNReal) : ℝ) =
      x (p.coeff n) * t ^ n := by
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (apply_nonneg x.toMulRingSeminorm _),
    GaussLaurent.coe_weight]

/-- A finite Laurent Gauss upper bound is the list of its weighted coefficient bounds. -/
theorem sectionPoint_polynomialMap_le_iff (x : BanachSpectrum A)
    (p : AddMonoidAlgebra A ℤ) (c : ℝ) (hc : 0 ≤ c) :
    sectionPoint K A t x (polynomialMap K A t p) ≤ c ↔
      ∀ n ∈ p.coeff.support, x (p.coeff n) * t ^ n ≤ c := by
  classical
  rw [sectionPoint_polynomialMap]
  constructor
  · intro h n hn
    have hle := Finset.le_sup (f := fun n =>
      Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n) hn
    have hreal : x (p.coeff n) * t ^ n ≤
        ↑(p.coeff.support.sup (fun n =>
          Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n)) := by
      simpa only [coe_weightedCoefficient] using (NNReal.coe_le_coe.mpr hle)
    exact hreal.trans h
  · intro h
    rw [← Real.coe_toNNReal c hc, NNReal.coe_le_coe]
    apply Finset.sup_le
    intro n hn
    apply NNReal.coe_le_coe.mp
    simpa only [coe_weightedCoefficient, Real.coe_toNNReal c hc] using h n hn

/-- A positive finite Laurent Gauss value is attained by a coefficient in its fixed support. -/
theorem exists_weightedCoefficient_eq_sectionPoint (x : BanachSpectrum A)
    (p : AddMonoidAlgebra A ℤ)
    (hp : 0 < sectionPoint K A t x (polynomialMap K A t p)) :
    ∃ n ∈ p.coeff.support,
      sectionPoint K A t x (polynomialMap K A t p) = x (p.coeff n) * t ^ n := by
  classical
  have hs : p.coeff.support.Nonempty := by
    by_contra h
    rw [sectionPoint_polynomialMap, Finset.not_nonempty_iff_eq_empty.mp h,
      Finset.sup_empty] at hp
    simp only [bot_eq_zero, NNReal.coe_zero, lt_self_iff_false] at hp
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup p.coeff.support hs
    (fun n => Real.toNNReal (x (p.coeff n)) * GaussLaurent.weight t n)
  refine ⟨n, hn, ?_⟩
  rw [sectionPoint_polynomialMap, heq, coe_weightedCoefficient]

omit [CompleteSpace K] in
private theorem coefficient_le_ratio_iff (a b c : ℝ) (n k : ℤ) :
    a ≤ (c * t ^ n / t ^ k) * b ↔ a * t ^ k ≤ c * (b * t ^ n) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (zpow_pos (Fact.out : 0 < t) k)]
  simp only [mul_comm, mul_left_comm]

omit [CompleteSpace K] in
/-- The chart selecting a fixed denominator coefficient to attain the Gauss maximum. -/
def polynomialRatioChart {I : Type v} [Fintype I]
    (f : I → AddMonoidAlgebra A ℤ) (g : AddMonoidAlgebra A ℤ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q) (n : ℤ) :
    RationalChart K A := by
  classical
  exact RationalChart.boundedRatios (g.coeff n) (q / t ^ n)
    (div_pos hq (zpow_pos (Fact.out : 0 < t) n))
    (Sum.elim (fun k : g.coeff.support => g.coeff k)
      (fun ik : Σ i, (f i).coeff.support => (f ik.1).coeff ik.2))
    (Sum.elim (fun k : g.coeff.support => t ^ n / t ^ (k : ℤ))
      (fun ik : Σ i, (f i).coeff.support => r ik.1 * t ^ n / t ^ (ik.2 : ℤ)))
    (by
      intro j
      cases j with
      | inl k =>
        exact div_pos (zpow_pos (Fact.out : 0 < t) n)
          (zpow_pos (Fact.out : 0 < t) (k : ℤ))
      | inr ik =>
        exact div_pos (mul_pos (hr _) (zpow_pos (Fact.out : 0 < t) n))
          (zpow_pos (Fact.out : 0 < t) (ik.2 : ℤ)))

omit [CompleteSpace K] in
theorem mem_locus_polynomialRatioChart {I : Type v} [Fintype I]
    (f : I → AddMonoidAlgebra A ℤ) (g : AddMonoidAlgebra A ℤ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q)
    (n : ℤ) (x : BanachSpectrum A) :
    x ∈ (polynomialRatioChart K t f g r hr q hq n).locus ↔
      q ≤ x (g.coeff n) * t ^ n ∧
      (∀ k ∈ g.coeff.support, x (g.coeff k) * t ^ k ≤ x (g.coeff n) * t ^ n) ∧
      ∀ i k, k ∈ (f i).coeff.support →
        x ((f i).coeff k) * t ^ k ≤ r i * (x (g.coeff n) * t ^ n) := by
  classical
  simp only [polynomialRatioChart, RationalChart.mem_locus_boundedRatios,
    Sum.forall, Sum.elim_inl, Sum.elim_inr, Sigma.forall, Subtype.forall,
    div_le_iff₀ (zpow_pos (Fact.out : 0 < t) n)]
  have hden (k : ℤ) :
      x (g.coeff k) ≤ t ^ n / t ^ k * x (g.coeff n) ↔
        x (g.coeff k) * t ^ k ≤ x (g.coeff n) * t ^ n := by
    simpa only [one_mul] using
      coefficient_le_ratio_iff t (x (g.coeff k)) (x (g.coeff n)) 1 n k
  simp only [hden, coefficient_le_ratio_iff]

/-- Positive-threshold finite Laurent rational inequalities split into finitely many
actual ambient rational charts, one for each fixed denominator-support exponent. -/
theorem polynomial_ratios_iff_exists_chart {I : Type v} [Fintype I]
    (f : I → AddMonoidAlgebra A ℤ) (g : AddMonoidAlgebra A ℤ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q)
    (x : BanachSpectrum A) :
    (q ≤ sectionPoint K A t x (polynomialMap K A t g) ∧
      ∀ i, sectionPoint K A t x (polynomialMap K A t (f i)) ≤
        r i * sectionPoint K A t x (polynomialMap K A t g)) ↔
      ∃ n ∈ g.coeff.support,
        x ∈ (polynomialRatioChart K t f g r hr q hq n).locus := by
  classical
  constructor
  · rintro ⟨hqg, hf⟩
    obtain ⟨n, hn, heq⟩ :=
      exists_weightedCoefficient_eq_sectionPoint K t x g (hq.trans_le hqg)
    refine ⟨n, hn, (mem_locus_polynomialRatioChart K t f g r hr q hq n x).mpr
      ⟨by rwa [← heq], ?_, ?_⟩⟩
    · have hmax := (sectionPoint_polynomialMap_le_iff K t x g _
        (apply_nonneg (sectionPoint K A t x).toMulRingSeminorm _)).mp le_rfl
      rwa [heq] at hmax
    · intro i k hk
      have hi := (sectionPoint_polynomialMap_le_iff K t x (f i) _
        (mul_nonneg (hr i).le
          (apply_nonneg (sectionPoint K A t x).toMulRingSeminorm _))).mp (hf i) k hk
      rwa [heq] at hi
  · rintro ⟨n, hn, hx⟩
    obtain ⟨hqn, hg, hf⟩ :=
      (mem_locus_polynomialRatioChart K t f g r hr q hq n x).mp hx
    have hnle : x (g.coeff n) * t ^ n ≤
        sectionPoint K A t x (polynomialMap K A t g) :=
      (sectionPoint_polynomialMap_le_iff K t x g _
        (apply_nonneg (sectionPoint K A t x).toMulRingSeminorm _)).mp le_rfl n hn
    have hgle : sectionPoint K A t x (polynomialMap K A t g) ≤
        x (g.coeff n) * t ^ n :=
      (sectionPoint_polynomialMap_le_iff K t x g _
        (hq.le.trans hqn)).mpr hg
    have heq := le_antisymm hgle hnle
    refine ⟨hqn.trans hnle, fun i => ?_⟩
    rw [heq]
    exact (sectionPoint_polynomialMap_le_iff K t x (f i) _
      (mul_nonneg (hr i).le (hq.le.trans hqn))).mpr (hf i)

/-- The coefficient decomposition as a family indexed by `Fin m`, including `m = 0`. -/
theorem exists_finite_polynomial_ratio_charts {I : Type v} [Fintype I]
    (f : I → AddMonoidAlgebra A ℤ) (g : AddMonoidAlgebra A ℤ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q) :
    ∃ (m : ℕ) (D : Fin m → RationalChart K A), ∀ x : BanachSpectrum A,
      (q ≤ sectionPoint K A t x (polynomialMap K A t g) ∧
        ∀ i, sectionPoint K A t x (polynomialMap K A t (f i)) ≤
          r i * sectionPoint K A t x (polynomialMap K A t g)) ↔
        ∃ j, x ∈ (D j).locus := by
  classical
  let e : g.coeff.support ≃ Fin (Fintype.card g.coeff.support) :=
    Fintype.equivFin g.coeff.support
  refine ⟨Fintype.card g.coeff.support,
    fun j => polynomialRatioChart K t f g r hr q hq (e.symm j), fun x => ?_⟩
  rw [polynomial_ratios_iff_exists_chart]
  constructor
  · rintro ⟨n, hn, hx⟩
    refine ⟨e ⟨n, hn⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hx
  · rintro ⟨j, hx⟩
    exact ⟨(e.symm j).val, (e.symm j).property, hx⟩

end Langlands.Analytic.RelativeLaurentAnnulus
