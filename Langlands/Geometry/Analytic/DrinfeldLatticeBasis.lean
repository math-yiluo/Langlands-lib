import Langlands.Geometry.Analytic.DrinfeldAdaptedBasis
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Normalized adapted bases near a lattice norm -/

noncomputable section

universe v w u u'

namespace Langlands.Analytic.VectorNorm

open Set
open scoped ENNReal

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]
  {ι : Type u} [Fintype ι] {ν μ : VectorNorm F V} {b : Module.Basis ι F V}

/-- A basis adapted to a norm and consisting of vectors of norm one. -/
def IsNormalizedBasis (μ : VectorNorm F V) (b : Module.Basis ι F V) : Prop :=
  μ.IsAdaptedBasis b ∧ ∀ i, μ (b i) = 1

/-- Comparing norms adapted to the same basis only requires checking its vectors. -/
theorem IsAdaptedBasis.ratioSup_le_ofReal_iff (hν : ν.IsAdaptedBasis b)
    (hμ : μ.IsAdaptedBasis b) {C : ℝ} (hC : 0 ≤ C) :
    ratioSup ν μ ≤ ENNReal.ofReal C ↔ ∀ i, ν (b i) ≤ C * μ (b i) := by
  constructor
  · intro h i
    have hp := μ.pos (b.ne_zero i)
    exact (div_le_iff₀ hp).1 ((ENNReal.ofReal_le_ofReal_iff hC).1 ((le_ratioSup ν μ (b i)).trans h))
  · intro h
    apply ratioSup_le_ofReal hC
    intro a _
    refine (hν.apply_le_iff (mul_nonneg hC (μ.nonneg a)) a).2 fun i => ?_
    calc ‖b.repr a i‖ * ν (b i) ≤ ‖b.repr a i‖ * (C * μ (b i)) :=
          mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
      _ = C * (‖b.repr a i‖ * μ (b i)) := by ring
      _ ≤ C * μ a := mul_le_mul_of_nonneg_left
        ((hμ.apply_le_iff (μ.nonneg a) a).1 le_rfl i) hC

/-- The ratio supremum is attained at a basis vector in a common adapted basis. -/
theorem IsAdaptedBasis.ratioSup_eq_of_basis_max (hν : ν.IsAdaptedBasis b)
    (hμ : μ.IsAdaptedBasis b) {i : ι} (hi : ∀ j, ν (b j) / μ (b j) ≤ ν (b i) / μ (b i)) :
    ratioSup ν μ = ENNReal.ofReal (ν (b i) / μ (b i)) :=
  le_antisymm ((hν.ratioSup_le_ofReal_iff hμ (div_nonneg (ν.nonneg _) (μ.nonneg _))).2
    fun j => (div_le_iff₀ (μ.pos (b.ne_zero j))).1 (hi j)) (le_ratioSup ν μ _)

/-- With a common adapted basis, the threshold comparison for the multiplicative distance
is equivalent to the strict coordinate pair comparisons. -/
theorem IsAdaptedBasis.distRatio_lt_iff (hν : ν.IsAdaptedBasis b)
    (hμ : μ.IsAdaptedBasis b) [Nonempty ι] {C : ℝ} (hC : 0 < C) :
    distRatio ν μ < ENNReal.ofReal C ↔
      ∀ i j, (ν (b i) / μ (b i)) * (μ (b j) / ν (b j)) < C := by
  have hp (i j : ι) : 0 ≤ ν (b i) / μ (b i) := div_nonneg (ν.nonneg _) (μ.nonneg _)
  constructor
  · intro h i j
    apply (ENNReal.ofReal_lt_ofReal_iff hC).1
    rw [ENNReal.ofReal_mul (hp i j)]
    exact (mul_le_mul' (le_ratioSup ν μ _) (le_ratioSup μ ν _)).trans_lt h
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
      (fun k => ν (b k) / μ (b k)) Finset.univ_nonempty
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
      (fun k => μ (b k) / ν (b k)) Finset.univ_nonempty
    rw [distRatio, hν.ratioSup_eq_of_basis_max hμ (fun k => hi k (Finset.mem_univ _)),
      hμ.ratioSup_eq_of_basis_max hν (fun k => hj k (Finset.mem_univ _)), ← ENNReal.ofReal_mul (hp i j)]
    exact (ENNReal.ofReal_lt_ofReal_iff hC).2 (h i j)

/-- Rescaling the members of an adapted basis by nonzero scalars preserves adaptedness. -/
theorem IsAdaptedBasis.unitsSMul (hb : ν.IsAdaptedBasis b) (u : ι → Fˣ) :
    ν.IsAdaptedBasis (b.unitsSMul u) := by
  intro c i
  simp only [Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul]
  exact hb (fun j => c j * (u j : F)) i

/-- Reindexing an adapted basis preserves adaptedness. -/
theorem IsAdaptedBasis.reindex (hb : ν.IsAdaptedBasis b) {ι' : Type u'} [Fintype ι']
    (e : ι ≃ ι') : ν.IsAdaptedBasis (b.reindex e) := by
  intro c i
  simp only [Module.Basis.reindex_apply]
  simpa only [Equiv.apply_symm_apply, ← e.symm.sum_comp (fun j => c (e j) • b j)]
    using hb (fun j => c (e j)) (e.symm i)

section Discrete

variable {k : Type v} [NontriviallyNormedField k] {ϖ : k}
  {E : Type w} [AddCommGroup E] [Module k E] {ν μ : VectorNorm k E}
  {b : Module.Basis ι k E}

/-- A basis adapted to a norm is also adapted to each of its rounded ball norms. -/
theorem IsAdaptedBasis.ballNorm (hb : ν.IsAdaptedBasis b) (hϖ : IsMaxBelowOne ϖ)
    {s : ℝ} (hs : 0 < s) : (VectorNorm.ballNorm hϖ ν hs).IsAdaptedBasis b := by
  intro c i
  by_cases h : c i • b i = 0
  · rw [h, map_zero]
    exact (VectorNorm.ballNorm hϖ ν hs).nonneg _
  change up ‖ϖ‖⁻¹ (ν (c i • b i) / s) ≤ up ‖ϖ‖⁻¹ (ν (∑ j, c j • b j) / s)
  exact up_mono hϖ.one_lt_inv (div_pos (ν.pos h) hs)
    (div_le_div_of_nonneg_right (hb c i) hs.le)

/-- When a lattice norm is strictly closer than `q = ‖ϖ‖⁻¹`, the two norms have a
common adapted basis, normalized for the lattice norm and sorted for the other norm. -/
theorem exists_normalized_sorted_basis_of_distRatio_lt [ProperSpace k]
    [FiniteDimensional k E] [Nontrivial E] {d : ℕ} (hN : Module.finrank k E = d + 1)
    (hϖ : IsMaxBelowOne ϖ) (hμ : μ.IsLatticeNorm)
    (hdist : distRatio ν μ < ENNReal.ofReal ‖ϖ‖⁻¹) :
    ∃ b : Module.Basis (Fin (d + 1)) k E,
      μ.IsNormalizedBasis b ∧ ν.IsAdaptedBasis b ∧ Monotone (fun i => ν (b i)) := by
  obtain ⟨a, ha⟩ := exists_ne (0 : E)
  obtain ⟨b, hb, -⟩ := ν.exists_isAdaptedBasis_with_first hN ha
  have hμb : μ.IsAdaptedBasis b := by
    obtain ⟨s, hs, rfl⟩ := eq_ballNorm hϖ ν hμ hdist
    exact hb.ballNorm hϖ hs
  choose t ht using fun i : Fin (d + 1) => hμ (b i)
  have ht0 (i : Fin (d + 1)) : t i ≠ 0 := by
    intro h
    have := ht i
    rw [h, norm_zero] at this
    exact (μ.pos (b.ne_zero i)).ne' this
  let u i := (Units.mk0 (t i) (ht0 i))⁻¹
  let B := b.unitsSMul u
  have hB (i : Fin (d + 1)) : μ (B i) = 1 := by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul]
    change ‖(t i)⁻¹‖ * μ (b i) = 1
    rw [norm_inv, ht i, inv_mul_cancel₀ (norm_ne_zero_iff.2 (ht0 i))]
  let e := Tuple.sort (fun i => ν (B i))
  refine ⟨B.reindex e.symm, ⟨(hμb.unitsSMul u).reindex e.symm, ?_⟩,
    (hb.unitsSMul u).reindex e.symm, ?_⟩
  · intro i
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using hB (e i)
  · intro i j hij
    simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
    exact (Tuple.monotone_sort (fun i => ν (B i))) hij

end Discrete

end Langlands.Analytic.VectorNorm
