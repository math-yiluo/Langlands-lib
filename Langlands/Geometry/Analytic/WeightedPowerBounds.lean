import Langlands.Geometry.Analytic.PowerBounds
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationDefinitions

/-! # Radius-weighted power bounds and finite monomial bounds -/

noncomputable section

universe u v

namespace Langlands.Analytic

/-- One positive constant bounds all actual powers relative to the given radius.
Applications use a strictly positive real radius; the empty power is included. -/
def HasRadiusBoundedPowers {A : Type u} [NormedRing A] (r : ℝ) (a : A) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * r ^ n

@[simp] theorem hasRadiusBoundedPowers_one {A : Type u} [NormedRing A] (a : A) :
    HasRadiusBoundedPowers 1 a ↔ HasBoundedPowers a := by
  simp only [HasRadiusBoundedPowers, one_pow, mul_one, HasBoundedPowers]

namespace HasRadiusBoundedPowers

variable {A : Type u} [NormedRing A] {r s : ℝ} {a : A}

theorem mono (ha : HasRadiusBoundedPowers r a) (hr : 0 ≤ r) (hrs : r ≤ s) :
    HasRadiusBoundedPowers s a := by
  obtain ⟨C, hC, hc⟩ := ha
  exact ⟨C, hC, fun n =>
    (hc n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs n) hC.le)⟩

/-- Nilpotents have weighted bounded powers at every strictly positive radius. -/
theorem of_isNilpotent (hr : 0 < r) (ha : IsNilpotent a) :
    HasRadiusBoundedPowers r a := by
  classical
  obtain ⟨d, hd⟩ := ha
  let C : ℝ := 1 + ∑ i ∈ Finset.range d, ‖a ^ i‖ / r ^ i
  have hsum : 0 ≤ ∑ i ∈ Finset.range d, ‖a ^ i‖ / r ^ i :=
    Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (pow_pos hr _).le
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one hsum
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < d
  · apply (div_le_iff₀ (pow_pos hr n)).mp
    exact (Finset.single_le_sum
      (fun i _ => div_nonneg (norm_nonneg _) (pow_pos hr i).le)
      (Finset.mem_range.mpr hn)).trans (le_add_of_nonneg_left zero_le_one)
  · rw [pow_eq_zero_of_le (Nat.le_of_not_gt hn) hd, norm_zero]
    exact mul_nonneg hC.le (pow_pos hr n).le

end HasRadiusBoundedPowers

/-- Bounded ring maps preserve the same radius-weighted power condition. -/
theorem BoundedRingHom.hasRadiusBoundedPowers_map {A : Type u} {B : Type v}
    [NormedCommRing A] [NormedCommRing B] (φ : BoundedRingHom A B)
    {r : ℝ} {a : A} (ha : HasRadiusBoundedPowers r a) :
    HasRadiusBoundedPowers r (φ a) := by
  obtain ⟨C, hC, hc⟩ := ha
  obtain ⟨D, hD, hd⟩ := φ.bounded
  refine ⟨D * C, mul_pos hD hC, fun n => ?_⟩
  change ‖φ.toRingHom a ^ n‖ ≤ _
  rw [← map_pow]
  exact (hd (a ^ n)).trans
    ((mul_le_mul_of_nonneg_left (hc n) hD.le).trans_eq (mul_assoc D C (r ^ n)).symm)

/-- The easy spectral implication needs neither completeness nor an affinoid
presentation, and does not assert the converse. -/
theorem HasRadiusBoundedPowers.spectrum_le {A : Type u} [NormedCommRing A]
    {r : ℝ} {a : A} (ha : HasRadiusBoundedPowers r a) (hr : 0 < r)
    (x : BanachSpectrum A) : x a ≤ r := by
  obtain ⟨C, _, hc⟩ := ha
  by_contra! h
  have hratio : 1 < x a / r := (one_lt_div hr).mpr h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  have hbound : (x a / r) ^ n ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hr n), ← map_pow x.toMulRingSeminorm]
    exact (x.le_norm (a ^ n)).trans (hc n)
  exact hn.not_ge hbound

namespace GeneralizedTateAlgebra

variable {σ : Type u} (r : PositivePolyradius σ) (B : Type v) [NormedCommRing B]

/-- A bounded monomial tuple bounds each coordinate's powers at its own radius. -/
theorem HasBoundedMonomials.radiusBoundedPowers {b : σ → B}
    (hb : HasBoundedMonomials r B b) (i : σ) :
    HasRadiusBoundedPowers (r i) (b i) := by
  classical
  obtain ⟨C, hC, hc⟩ := hb
  refine ⟨C, hC, fun n => ?_⟩
  simpa [StrictTateAlgebra.monomialValue, PositivePolyradius.weight] using
    hc (Finsupp.single i n)

/-- For finitely many variables, individual radius-weighted power bounds are
equivalent to one uniform bound on all weighted monomials. -/
theorem hasBoundedMonomials_iff_radiusBoundedPowers [Fintype σ] (b : σ → B) :
    HasBoundedMonomials r B b ↔ ∀ i, HasRadiusBoundedPowers (r i) (b i) := by
  classical
  constructor
  · exact fun h i => h.radiusBoundedPowers r B i
  · intro h
    choose C hC hc using h
    let D : ℝ := max 1 (max ‖(1 : B)‖ (∏ i, C i))
    have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨D, hD, fun d => ?_⟩
    unfold StrictTateAlgebra.monomialValue PositivePolyradius.weight
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rcases (Finset.univ : Finset σ).eq_empty_or_nonempty with hempty | hnonempty
    · rw [hempty, Finset.prod_empty, Finset.prod_empty, mul_one]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · calc
        ‖∏ i, b i ^ d i‖ ≤ ∏ i, ‖b i ^ d i‖ := Finset.norm_prod_le' _ hnonempty _
        _ ≤ ∏ i, C i * r i ^ d i :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hc i (d i))
        _ = (∏ i, C i) * ∏ i, r i ^ d i := Finset.prod_mul_distrib
        _ ≤ D * ∏ i, r i ^ d i :=
          mul_le_mul_of_nonneg_right
            ((le_max_right _ _).trans (le_max_right _ _))
            (Finset.prod_nonneg fun i _ => (pow_pos (r.positive i) _).le)

end GeneralizedTateAlgebra

end Langlands.Analytic
