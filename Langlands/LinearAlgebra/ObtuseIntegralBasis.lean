import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

/-! # Short vectors in an obtuse even integral lattice -/

noncomputable section

universe uM uI

namespace Langlands.LinearAlgebra

variable {M : Type uM} [AddCommGroup M] [Module ℝ M]

/-- A real bilinear form is integral on a lattice, with even squared lengths. -/
def IsEvenIntegralOn (B : LinearMap.BilinForm ℝ M) (L : Submodule ℤ M) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, B x y = (n : ℝ)) ∧
  (∀ x ∈ L, ∃ n : ℤ, B x x = 2 * (n : ℝ))

/-- Integral pairings on generators extend to the integer span. -/
theorem exists_int_bilin_of_mem_span (B : LinearMap.BilinForm ℝ M)
    (S : Set M) (hS : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, B x y = (n : ℝ))
    {x y : M} (hx : x ∈ Submodule.span ℤ S) (hy : y ∈ Submodule.span ℤ S) :
    ∃ n : ℤ, B x y = (n : ℝ) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy => exact hS x hx y hy
  | zero_left y hy => exact ⟨0, by simp⟩
  | zero_right x hx => exact ⟨0, by simp⟩
  | add_left x₁ x₂ y hx₁ hx₂ hy h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁
    obtain ⟨n₂, hn₂⟩ := h₂
    exact ⟨n₁ + n₂, by simp [hn₁, hn₂]⟩
  | add_right x y₁ y₂ hx hy₁ hy₂ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁
    obtain ⟨n₂, hn₂⟩ := h₂
    exact ⟨n₁ + n₂, by simp [hn₁, hn₂]⟩
  | smul_left n x y hx hy h =>
    obtain ⟨m, hm⟩ := h
    exact ⟨n * m, by simp [map_zsmul, hm]⟩
  | smul_right n x y hx hy h =>
    obtain ⟨m, hm⟩ := h
    exact ⟨n * m, by simp [map_zsmul, hm]⟩

/-- A symmetric integral Gram matrix with even diagonal generates an even
integral lattice. -/
theorem isEvenIntegralOn_span (B : LinearMap.BilinForm ℝ M)
    (hsymm : ∀ x y, B x y = B y x) (S : Set M)
    (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, B x y = (n : ℝ))
    (heven : ∀ x ∈ S, ∃ n : ℤ, B x x = 2 * (n : ℝ)) :
    IsEvenIntegralOn B (Submodule.span ℤ S) := by
  refine ⟨fun _ hx _ hy => exists_int_bilin_of_mem_span B S hint hx hy, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact heven x hx
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy hxe hye =>
    obtain ⟨m, hm⟩ := hxe
    obtain ⟨n, hn⟩ := hye
    obtain ⟨k, hk⟩ := exists_int_bilin_of_mem_span B S hint hx hy
    refine ⟨m + n + k, ?_⟩
    simp only [map_add, LinearMap.add_apply, hsymm y x, hm, hn, hk, Int.cast_add]
    ring
  | smul n x hx hxe =>
    obtain ⟨m, hm⟩ := hxe
    refine ⟨n * n * m, ?_⟩
    simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, hm, Int.cast_mul]
    ring

/-- Positive squared lengths in an even integral lattice are at least two. -/
theorem two_le_bilin_self_of_pos {B : LinearMap.BilinForm ℝ M}
    {L : Submodule ℤ M} (hL : IsEvenIntegralOn B L)
    {x : M} (hx : x ∈ L) (hpos : 0 < B x x) : 2 ≤ B x x := by
  obtain ⟨n, hn⟩ := hL.2 x hx
  have hnpos : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  linarith

section Finite

variable {ι : Type uI} [Fintype ι] (b : ι → M)

/-- A nonzero integer combination of a real independent family stays nonzero. -/
theorem sum_zsmul_ne_zero_of_coeff_ne_zero (hli : LinearIndependent ℝ b)
    (n : ι → ℤ) {i : ι} (hi : n i ≠ 0) : ∑ j, n j • b j ≠ 0 := by
  intro hzero
  have hreal : ∑ j, (n j : ℝ) • b j = 0 := by
    simpa only [Int.cast_smul_eq_zsmul] using hzero
  have := Fintype.linearIndependent_iff.mp hli (fun j => (n j : ℝ)) hreal i
  exact hi (Int.cast_eq_zero.mp this)

/-- Disjoint nonnegative combinations of an obtuse family have nonpositive
mutual pairing. -/
theorem bilin_sum_zsmul_nonpos_of_disjoint (B : LinearMap.BilinForm ℝ M)
    (hobt : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0)
    (p q : ι → ℤ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hdisj : ∀ i, p i = 0 ∨ q i = 0) :
    B (∑ i, p i • b i) (∑ j, q j • b j) ≤ 0 := by
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    zsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  by_cases hij : i = j
  · subst j
    rcases hdisj i with hi | hi <;> simp [hi]
  · exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hq i)
      (mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hp j) (hobt j i (Ne.symm hij)))

/-- A vector of squared length two has integer coordinates of one sign in an
independent obtuse family generating an even integral lattice. -/
theorem same_sign_of_bilin_self_eq_two (B : LinearMap.BilinForm ℝ M)
    (hsymm : ∀ x y, B x y = B y x)
    (hpos : ∀ x : M, x ≠ 0 → 0 < B x x)
    (hli : LinearIndependent ℝ b)
    (heven : IsEvenIntegralOn B (Submodule.span ℤ (Set.range b)))
    (hobt : ∀ i j, i ≠ j → B (b i) (b j) ≤ 0)
    (n : ι → ℤ) (hlen : B (∑ i, n i • b i) (∑ i, n i • b i) = 2) :
    (∀ i, 0 ≤ n i) ∨ (∀ i, n i ≤ 0) := by
  classical
  by_contra hsign
  push Not at hsign
  obtain ⟨⟨i, hi⟩, j, hj⟩ := hsign
  let p : ι → ℤ := fun k => max (n k) 0
  let q : ι → ℤ := fun k => max (-n k) 0
  let x : M := ∑ k, p k • b k
  let y : M := ∑ k, q k • b k
  have hp : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
  have hq : ∀ k, 0 ≤ q k := fun k => le_max_right _ _
  have hdisj : ∀ k, p k = 0 ∨ q k = 0 := by
    intro k
    dsimp [p, q]
    omega
  have hsub : (∑ k, n k • b k) = x - y := by
    dsimp [x, y]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← sub_smul]
    congr 1
    dsimp [p, q]
    omega
  have hxmem : x ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hymem : y ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hxne : x ≠ 0 := sum_zsmul_ne_zero_of_coeff_ne_zero b hli p
    (i := j) (by dsimp [p]; omega)
  have hyne : y ≠ 0 := sum_zsmul_ne_zero_of_coeff_ne_zero b hli q
    (i := i) (by dsimp [q]; omega)
  have hxlen := two_le_bilin_self_of_pos heven hxmem (hpos x hxne)
  have hylen := two_le_bilin_self_of_pos heven hymem (hpos y hyne)
  have hxy : B x y ≤ 0 :=
    bilin_sum_zsmul_nonpos_of_disjoint b B hobt p q hp hq hdisj
  rw [hsub] at hlen
  simp only [map_sub, LinearMap.sub_apply, hsymm y x] at hlen
  linarith

end Finite

end Langlands.LinearAlgebra
