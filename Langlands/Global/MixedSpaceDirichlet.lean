import Langlands.Global.NormOneIdeleClassCompact
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-! # Simultaneous Dirichlet approximation at the infinite places of a number field -/

noncomputable section

universe u

namespace Langlands.Global.MixedSpaceDirichlet

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

variable (F : Type u) [Field F] [NumberField F]

/-- The index type of the chosen integral basis. -/
abbrev Index := Free.ChooseBasisIndex ℤ (𝓞 F)

/-- A bound for the place norms of the image of the chosen integral basis. -/
def basisBound : ℝ :=
  ∑ i : Index F, ∑ w : InfinitePlace F, normAtPlace w (latticeBasis F i)

omit [NumberField F] in
theorem normAtPlace_sum_le {α : Type*} (s : Finset α) (f : α → mixedSpace F)
    (w : InfinitePlace F) :
    normAtPlace w (∑ i ∈ s, f i) ≤ ∑ i ∈ s, normAtPlace w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAtPlace_add_le w _ _).trans (add_le_add le_rfl ih)

/-- Real combinations of the lattice basis with coefficients bounded by `ε`
have every place norm bounded by `ε * basisBound F`. -/
theorem normAtPlace_combination_le (c : Index F → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ i, |c i| ≤ ε) (w : InfinitePlace F) :
    normAtPlace w (∑ i, c i • latticeBasis F i) ≤ ε * basisBound F := by
  calc normAtPlace w (∑ i, c i • latticeBasis F i)
      ≤ ∑ i, normAtPlace w (c i • latticeBasis F i) := normAtPlace_sum_le F _ _ w
    _ = ∑ i, |c i| * normAtPlace w (latticeBasis F i) := by
        simp only [normAtPlace_smul]
    _ ≤ ∑ i, ε * normAtPlace w (latticeBasis F i) := by
        gcongr with i
        · exact normAtPlace_nonneg _ _
        · exact hc i
    _ = ε * ∑ i, normAtPlace w (latticeBasis F i) := by rw [Finset.mul_sum]
    _ ≤ ε * basisBound F := by
        gcongr
        exact Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun w' => normAtPlace w' (latticeBasis F i))
            (fun w' _ => normAtPlace_nonneg _ _) (Finset.mem_univ w)

/-- Every integer combination of the lattice basis is the mixed embedding of an
algebraic integer. -/
theorem exists_integer_eq_combination (c : Index F → ℤ) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = ∑ i, (c i : ℝ) • latticeBasis F i := by
  have hmem : ∑ i, (c i : ℝ) • latticeBasis F i ∈
      Submodule.span ℤ (Set.range (latticeBasis F)) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul ℝ (c i) (latticeBasis F i)]
    exact Submodule.smul_mem _ (c i) (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a, ha⟩ := (mem_span_latticeBasis F).mp hmem
  exact ⟨a, ha⟩

theorem card_index_pos : 0 < Fintype.card (Index F) := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  exact Module.finrank_pos

/-- **Simultaneous Dirichlet approximation.** For every point `z` of the mixed
space and every positive integer `N`, there are algebraic integers `l` and
`m ≠ 0` with `m` of size at most `N * basisBound F` and `l + m z` of size at most
`basisBound F / N` at every infinite place. -/
theorem exists_dirichlet (z : mixedSpace F) (N : ℕ) (hN : 0 < N) :
    ∃ l m : 𝓞 F, m ≠ 0 ∧ ∀ w : InfinitePlace F,
      normAtPlace w (mixedEmbedding F (m : F)) ≤ N * basisBound F ∧
      normAtPlace w (mixedEmbedding F (l : F) + mixedEmbedding F (m : F) * z) ≤
        basisBound F / N := by
  classical
  set b := latticeBasis F
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  choose pt hpt using exists_integer_eq_combination F
  let coord : (Index F → Fin (N + 1)) → Index F → ℝ := fun a i =>
    b.repr (mixedEmbedding F (pt (fun j => ((a j : ℕ) : ℤ)) : F) * z) i
  have hcell (t : ℝ) : (⌊(N : ℝ) * Int.fract t⌋).toNat < N := by
    have h0 : 0 ≤ ⌊(N : ℝ) * Int.fract t⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hNr.le (Int.fract_nonneg t))
    have h1 : (N : ℝ) * Int.fract t < ((N : ℤ) : ℝ) := by
      rw [Int.cast_natCast]
      exact mul_lt_of_lt_one_right hNr (Int.fract_lt_one t)
    have h2 : ⌊(N : ℝ) * Int.fract t⌋ < (N : ℤ) := Int.floor_lt.mpr h1
    omega
  let cell : (Index F → Fin (N + 1)) → Index F → Fin N := fun a i =>
    ⟨(⌊(N : ℝ) * Int.fract (coord a i)⌋).toNat, hcell _⟩
  have hcard : Fintype.card (Index F → Fin N) < Fintype.card (Index F → Fin (N + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self N) (card_index_pos F).ne'
  obtain ⟨a, a', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt cell hcard
  -- closeness of fractional parts
  have hclose (i : Index F) : |Int.fract (coord a i) - Int.fract (coord a' i)| ≤ 1 / N := by
    have hi := congrFun heq i
    simp only [cell, Fin.mk.injEq] at hi
    have hf : ⌊(N : ℝ) * Int.fract (coord a i)⌋ = ⌊(N : ℝ) * Int.fract (coord a' i)⌋ := by
      have h0 : 0 ≤ ⌊(N : ℝ) * Int.fract (coord a i)⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg hNr.le (Int.fract_nonneg _))
      have h0' : 0 ≤ ⌊(N : ℝ) * Int.fract (coord a' i)⌋ :=
        Int.floor_nonneg.mpr (mul_nonneg hNr.le (Int.fract_nonneg _))
      omega
    have h := (Int.abs_sub_lt_one_of_floor_eq_floor hf).le
    rw [← mul_sub, abs_mul, abs_of_pos hNr] at h
    rw [le_div_iff₀ hNr]
    linarith
  let cm : Index F → ℤ := fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)
  let cl : Index F → ℤ := fun i => -(⌊coord a i⌋ - ⌊coord a' i⌋)
  refine ⟨pt cl, pt cm, ?_, fun w => ⟨?_, ?_⟩⟩
  · intro hm
    apply hne
    have h0 : ∑ i, (cm i : ℝ) • b i = 0 := by
      rw [← hpt cm, hm]
      simp
    have hli := Fintype.linearIndependent_iff.mp b.linearIndependent _ h0
    funext i
    apply Fin.ext
    have := hli i
    simp only [cm, Int.cast_sub, Int.cast_natCast, sub_eq_zero] at this
    exact_mod_cast this
  · rw [hpt cm]
    refine normAtPlace_combination_le F _ hNr.le (fun i => ?_) w
    have ha := (a i).isLt
    have ha' := (a' i).isLt
    simp only [cm, Int.cast_sub, Int.cast_natCast]
    rw [abs_le]
    constructor
    · have : ((a i : ℕ) : ℝ) ≥ 0 := Nat.cast_nonneg _
      have : ((a' i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp ha'
      linarith
    · have : ((a' i : ℕ) : ℝ) ≥ 0 := Nat.cast_nonneg _
      have : ((a i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp ha
      linarith
  · have hdiff : mixedEmbedding F (pt cm : F) * z =
        mixedEmbedding F (pt (fun j => ((a j : ℕ) : ℤ)) : F) * z -
          mixedEmbedding F (pt (fun j => ((a' j : ℕ) : ℤ)) : F) * z := by
      rw [← sub_mul, hpt, hpt, hpt, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cm, Int.cast_sub, sub_smul]
    have hvec : mixedEmbedding F (pt cl : F) + mixedEmbedding F (pt cm : F) * z =
        ∑ i, (Int.fract (coord a i) - Int.fract (coord a' i)) • b i := by
      rw [hpt cl, hdiff, ← b.sum_repr (mixedEmbedding F (pt (fun j => ((a j : ℕ) : ℤ)) : F) * z
          - mixedEmbedding F (pt (fun j => ((a' j : ℕ) : ℤ)) : F) * z),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← add_smul]
      congr 1
      simp only [cl, coord, map_sub, Finsupp.coe_sub, Pi.sub_apply, Int.cast_neg,
        Int.cast_sub, Int.fract]
      ring
    rw [hvec, div_eq_mul_inv, mul_comm, ← one_div]
    exact normAtPlace_combination_le F _ (by positivity) hclose w

/-- The same approximation on the actual infinite adele ring, with the actual
place norms of its completions. -/
theorem exists_dirichlet_infiniteAdeles (y : InfiniteAdeles F) (N : ℕ) (hN : 0 < N) :
    ∃ l m : 𝓞 F, m ≠ 0 ∧ ∀ w : InfinitePlace F,
      ‖algebraMap F (InfiniteAdeles F) (m : F) w‖ ≤ N * basisBound F ∧
      ‖(algebraMap F (InfiniteAdeles F) (l : F) +
          algebraMap F (InfiniteAdeles F) (m : F) * y) w‖ ≤ basisBound F / N := by
  obtain ⟨l, m, hm, h⟩ :=
    exists_dirichlet F (InfiniteAdeleRing.ringEquiv_mixedSpace F y) N hN
  refine ⟨l, m, hm, fun w => ?_⟩
  rw [← NormOneIdeleClass.normAtPlace_ringEquiv_mixedSpace,
    ← NormOneIdeleClass.normAtPlace_ringEquiv_mixedSpace, map_add, map_mul,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
    ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact h w

end Langlands.Global.MixedSpaceDirichlet
