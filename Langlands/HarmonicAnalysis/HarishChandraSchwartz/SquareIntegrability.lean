import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Square integrability of `Ξ` against a power of `1 + σ` (Lemma II.1.5)

Waldspurger 2003, Lemma II.1.5: there is `d ∈ ℕ` such that
`∫_G Ξ(g)² (1 + σ(g))^{-d} dg` converges. The proof uses the Cartan decomposition
`G = ⋃_m K m K` (I.1 (4)), the bound `mes(K m K) ≤ C δ₀(m)⁻¹` (I.1 (5)), the upper bound
`Ξ(m) ≤ C δ₀(m)^{1/2} (1 + σ(m))^{d'}` of Lemma II.1.1, and the comparison
`1 + |H₀(m)| ≤ C (1 + σ(m))` of I.1 (6) with the lattice `H₀(M₀)`. This module states the
conclusion as `SquareIntegrableWeight`, collects these inputs for abstract cells, weights
and a lattice in `CartanSquareBound`, and proves that they imply the conclusion.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace Langlands.HarishChandraSchwartz

universe u v w

section Statement

variable {G : Type u} [MeasurableSpace G]

/-- The conclusion of Lemma II.1.5 of Waldspurger, for weights `Ξ σ : G → ℝ` and a
measure `μ`: there is `d ∈ ℕ` with `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞`. -/
def SquareIntegrableWeight (μ : Measure G) (Ξ σ : G → ℝ) : Prop :=
  ∃ d : ℕ, ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ < ⊤

end Statement

section Cartan

variable {G : Type u} [MeasurableSpace G] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {ι : Type w}

/-- The inputs of the proof of Lemma II.1.5 of Waldspurger, for a measure `μ`, weights
`Ξ σ : G → ℝ`, a family of cells `cell : ι → Set G` (the double cosets `K m K` with
`m ∈ M̄₀⁺ / M₀¹`), a subgroup `L` of a real normed space `E` (the lattice `H₀(M₀)` in
`a₀`), a map `H : ι → L` (the map `m ↦ H₀(m)`) and `δ : ι → ℝ` (the values `δ₀(m)`):

* `ι` is countable and the cells cover `G` (I.1 (4));
* `σ ≥ 0` and `δ > 0`;
* `μ(cell i) ≤ C δ(i)⁻¹` (the upper bound of I.1 (5));
* `|Ξ(g)| ≤ C δ(i)^{1/2} (1 + σ(g))^{d'}` for `g ∈ cell i` (the upper bound of
  Lemma II.1.1, transported to the double coset by bi-`K`-invariance);
* `1 + ‖H(i)‖ ≤ C (1 + σ(g))` for `g ∈ cell i`, with `C > 0` (the lower bound of
  I.1 (6), transported in the same way);
* `H` is injective. -/
structure CartanSquareBound (μ : Measure G) (Ξ σ : G → ℝ) (cell : ι → Set G)
    (L : Submodule ℤ E) (H : ι → L) (δ : ι → ℝ) : Prop where
  countable : Countable ι
  iUnion_cell : ⋃ i, cell i = univ
  sigma_nonneg : ∀ g, 0 ≤ σ g
  delta_pos : ∀ i, 0 < δ i
  measure_cell_le : ∃ C : ℝ≥0, ∀ i, μ (cell i) ≤ C * ENNReal.ofReal (δ i)⁻¹
  abs_xi_le : ∃ C d : ℝ, ∀ i, ∀ g ∈ cell i, |Ξ g| ≤ C * Real.sqrt (δ i) * (1 + σ g) ^ d
  one_add_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ g ∈ cell i, 1 + ‖H i‖ ≤ C * (1 + σ g)
  injective : Function.Injective H

omit [NormedSpace ℝ E] in
/-- If `Ξ` and `σ` are constant on each cell, with value at a point `m i ∈ cell i`, the
bounds of `CartanSquareBound` only need to hold at the points `m i`. This is the form in
which Waldspurger states I.1 (5), I.1 (6) and Lemma II.1.1, for `m ∈ M̄₀⁺`. -/
theorem CartanSquareBound.of_representatives {μ : Measure G} {Ξ σ : G → ℝ}
    {cell : ι → Set G} {L : Submodule ℤ E} {H : ι → L} {δ : ι → ℝ} (m : ι → G)
    (hcount : Countable ι) (hcover : ⋃ i, cell i = univ) (hσ : ∀ g, 0 ≤ σ g)
    (hδ : ∀ i, 0 < δ i)
    (hconst : ∀ i, ∀ g ∈ cell i, Ξ g = Ξ (m i) ∧ σ g = σ (m i))
    (hmeas : ∃ C : ℝ≥0, ∀ i, μ (cell i) ≤ C * ENNReal.ofReal (δ i)⁻¹)
    (hxi : ∃ C d : ℝ, ∀ i, |Ξ (m i)| ≤ C * Real.sqrt (δ i) * (1 + σ (m i)) ^ d)
    (hnorm : ∃ C : ℝ, 0 < C ∧ ∀ i, 1 + ‖H i‖ ≤ C * (1 + σ (m i)))
    (hinj : Function.Injective H) :
    CartanSquareBound μ Ξ σ cell L H δ := by
  obtain ⟨C₂, d, hC₂⟩ := hxi
  obtain ⟨C₆, hC₆, hC₆'⟩ := hnorm
  refine ⟨hcount, hcover, hσ, hδ, hmeas, ⟨C₂, d, fun i g hg => ?_⟩,
    ⟨C₆, hC₆, fun i g hg => ?_⟩, hinj⟩
  · rw [(hconst i g hg).1, (hconst i g hg).2]
    exact hC₂ i
  · rw [(hconst i g hg).2]
    exact hC₆' i

variable [FiniteDimensional ℝ E]

/-- For `s > rank L`, the series `∑_{z ∈ L} (1 + ‖z‖)^{-s}` converges. -/
theorem summable_one_add_norm_rpow_neg (L : Submodule ℤ E) [DiscreteTopology L] {s : ℝ}
    (hs : (Module.finrank ℤ L : ℝ) < s) :
    Summable fun z : L => (1 + ‖z‖) ^ (-s) := by
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  refine Summable.of_norm_bounded_eventually
    (ZLattice.summable_norm_rpow L (-s) (by linarith)) ?_
  filter_upwards [(Set.finite_singleton (0 : L)).compl_mem_cofinite] with z hz
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos hz' (by linarith) (by linarith)

/-- **Waldspurger, Lemma II.1.5**, from the inputs collected in `CartanSquareBound`:
there is `d ∈ ℕ` with `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞`. -/
theorem CartanSquareBound.squareIntegrableWeight {μ : Measure G} {Ξ σ : G → ℝ}
    {cell : ι → Set G} {L : Submodule ℤ E} [DiscreteTopology L] {H : ι → L} {δ : ι → ℝ}
    (h : CartanSquareBound μ Ξ σ cell L H δ) : SquareIntegrableWeight μ Ξ σ := by
  have := h.countable
  obtain ⟨C₅, hC₅⟩ := h.measure_cell_le
  obtain ⟨C₂, d₁, hC₂⟩ := h.abs_xi_le
  obtain ⟨C₆, hC₆, hC₆'⟩ := h.one_add_norm_le
  set r : ℝ := (Module.finrank ℤ L : ℝ)
  set d : ℕ := ⌈2 * d₁ + r + 1⌉₊
  set s : ℝ := (d : ℝ) - 2 * d₁
  have hs : r < s := by
    have := Nat.le_ceil (2 * d₁ + r + 1)
    simp only [s]
    linarith
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg _) hs.le
  set A : ℝ := C₂ ^ 2 * C₆ ^ s
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hC₆.le _)
  -- Pointwise bound on a cell.
  have key : ∀ i, ∀ g ∈ cell i,
      ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ≤
        ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) := by
    intro i g hg
    apply ENNReal.ofReal_le_ofReal
    have ht : 0 < 1 + σ g := by linarith [h.sigma_nonneg g]
    have hn : 0 < 1 + ‖H i‖ := by positivity
    have hδ := h.delta_pos i
    have hB := hC₂ i g hg
    have hsq : Ξ g ^ 2 ≤ C₂ ^ 2 * δ i * (1 + σ g) ^ (2 * d₁) := by
      have h1 : Ξ g ^ 2 ≤ (C₂ * Real.sqrt (δ i) * (1 + σ g) ^ d₁) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      have h3 : ((1 + σ g) ^ d₁) ^ 2 = (1 + σ g) ^ (2 * d₁) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        congr 1
        push_cast
        ring
      have h2 : (C₂ * Real.sqrt (δ i) * (1 + σ g) ^ d₁) ^ 2 =
          C₂ ^ 2 * δ i * (1 + σ g) ^ (2 * d₁) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hδ.le, h3]
      linarith
    have hpow : (1 + σ g) ^ (2 * d₁) * (1 + σ g) ^ (-(d : ℝ)) = (1 + σ g) ^ (-s) := by
      rw [← Real.rpow_add ht]
      congr 1
      simp only [s]
      ring
    have hcmp : (1 + σ g) ^ (-s) ≤ C₆ ^ s * (1 + ‖H i‖) ^ (-s) := by
      have hle : (1 + ‖H i‖) / C₆ ≤ 1 + σ g := by
        rw [div_le_iff₀ hC₆]
        linarith [hC₆' i g hg]
      calc (1 + σ g) ^ (-s) ≤ ((1 + ‖H i‖) / C₆) ^ (-s) :=
            Real.rpow_le_rpow_of_nonpos (div_pos hn hC₆) hle (by linarith)
        _ = C₆ ^ s * (1 + ‖H i‖) ^ (-s) := by
            rw [Real.div_rpow hn.le hC₆.le, Real.rpow_neg hC₆.le, div_inv_eq_mul, mul_comm]
    have hpos : 0 ≤ (1 + σ g) ^ (-(d : ℝ)) := Real.rpow_nonneg ht.le _
    calc Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))
        ≤ C₂ ^ 2 * δ i * (1 + σ g) ^ (2 * d₁) * (1 + σ g) ^ (-(d : ℝ)) :=
          mul_le_mul_of_nonneg_right hsq hpos
      _ = C₂ ^ 2 * δ i * (1 + σ g) ^ (-s) := by rw [mul_assoc, hpow]
      _ ≤ C₂ ^ 2 * δ i * (C₆ ^ s * (1 + ‖H i‖) ^ (-s)) :=
          mul_le_mul_of_nonneg_left hcmp (mul_nonneg (sq_nonneg _) hδ.le)
      _ = δ i * (A * (1 + ‖H i‖) ^ (-s)) := by simp only [A]; ring
  -- The factor `δ(i)` cancels against the measure of the cell.
  have hcell : ∀ i, ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) * μ (cell i) ≤
      C₅ * ENNReal.ofReal (A * (1 + ‖H i‖) ^ (-s)) := by
    intro i
    have hδ := h.delta_pos i
    have hX : 0 ≤ A * (1 + ‖H i‖) ^ (-s) :=
      mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
    calc ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) * μ (cell i)
        ≤ ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) *
            (C₅ * ENNReal.ofReal (δ i)⁻¹) := by gcongr; exact hC₅ i
      _ = C₅ * (ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) *
            ENNReal.ofReal (δ i)⁻¹) := by ring
      _ = C₅ * ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s)) * (δ i)⁻¹) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hδ.le hX)]
      _ = C₅ * ENNReal.ofReal (A * (1 + ‖H i‖) ^ (-s)) := by
          rw [mul_comm (δ i), mul_assoc, mul_inv_cancel₀ hδ.ne', mul_one]
  have hsum : Summable fun z : L => A * (1 + ‖z‖) ^ (-s) :=
    (summable_one_add_norm_rpow_neg L hs).mul_left A
  refine ⟨d, ?_⟩
  calc ∫⁻ g, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ
      = ∫⁻ g in ⋃ i, cell i, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ := by
        rw [h.iUnion_cell, setLIntegral_univ]
    _ ≤ ∑' i, ∫⁻ g in cell i, ENNReal.ofReal (Ξ g ^ 2 * (1 + σ g) ^ (-(d : ℝ))) ∂μ :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' i, ENNReal.ofReal (δ i * (A * (1 + ‖H i‖) ^ (-s))) * μ (cell i) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← setLIntegral_const]
        exact setLIntegral_mono measurable_const (key i)
    _ ≤ ∑' i, C₅ * ENNReal.ofReal (A * (1 + ‖H i‖) ^ (-s)) :=
        ENNReal.tsum_le_tsum hcell
    _ = C₅ * ∑' i, ENNReal.ofReal (A * (1 + ‖H i‖) ^ (-s)) := ENNReal.tsum_mul_left
    _ ≤ C₅ * ∑' z : L, ENNReal.ofReal (A * (1 + ‖z‖) ^ (-s)) :=
        by
          gcongr
          exact ENNReal.tsum_comp_le_tsum_of_injective h.injective
            (fun z : L => ENNReal.ofReal (A * (1 + ‖z‖) ^ (-s)))
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg hA
          (Real.rpow_nonneg (by positivity) _)) hsum]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top

end Cartan

end Langlands.HarishChandraSchwartz
