import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Signed differentials on finite commuting cut diagrams. -/

noncomputable section

namespace Langlands.Aubert.CutComplex

open scoped BigOperators

universe uI uM

variable {ι : Type uI} [LinearOrder ι]

/-- Position of a cut in the increasing order on the target cut set. -/
def position (s : Finset ι) (i : ι) : ℕ := (s.filter (· < i)).card

/-- The exterior insertion sign for an increasing cut basis. -/
def sign (s : Finset ι) (i : ι) : ℂ := (-1 : ℂ) ^ position s i

theorem position_erase_of_lt {s : Finset ι} {i j : ι} (hi : i ∈ s) (hij : i < j) :
    position (s.erase i) j + 1 = position s j := by
  simp only [position, Finset.filter_erase]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hi, hij⟩)

theorem position_erase_of_not_lt (s : Finset ι) {i j : ι} (hij : ¬ i < j) :
    position (s.erase i) j = position s j := by
  simp [position, Finset.filter_erase, Finset.erase_eq_of_notMem, hij]

theorem sign_pair {s : Finset ι} {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    sign s i * sign (s.erase i) j = -(sign s j * sign (s.erase j) i) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hcount := position_erase_of_lt hi hij
    have hother := position_erase_of_not_lt s (not_lt_of_ge hij.le)
    simp only [sign, hother]
    rw [← hcount, pow_succ]
    ring
  · have hcount := position_erase_of_lt hj hji
    have hother := position_erase_of_not_lt s (not_lt_of_ge hji.le)
    simp only [sign, hother]
    rw [← hcount, pow_succ]
    ring

/-- A diagram of actual complex vector spaces on the inclusion order of cuts. -/
structure Diagram (ι : Type uI) [LinearOrder ι] where
  Obj : Finset ι → Type uM
  add : ∀ s, AddCommGroup (Obj s)
  module : ∀ s, Module ℂ (Obj s)
  map : ∀ {s t : Finset ι}, s ⊆ t → Obj s →ₗ[ℂ] Obj t
  map_refl : ∀ s, map (s := s) Finset.Subset.rfl = LinearMap.id
  map_comp : ∀ {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u),
    (map htu).comp (map hst) = map (hst.trans htu)

attribute [instance] Diagram.add Diagram.module

namespace Diagram

variable (D : Diagram.{uI,uM} ι)

/-- The finite total product of the cut terms. -/
abbrev Total := ∀ s : Finset ι, D.Obj s

@[simp]
theorem map_map {s t u : Finset ι} (hst : s ⊆ t) (htu : t ⊆ u) (v : D.Obj s) :
    D.map htu (D.map hst v) = D.map (hst.trans htu) v :=
  LinearMap.congr_fun (D.map_comp hst htu) v

theorem map_apply_congr {s t u : Finset ι} (h : s = t) (hs : s ⊆ u) (ht : t ⊆ u)
    (x : D.Total) : D.map hs (x s) = D.map ht (x t) := by
  subst t
  rfl

/-- The elementary signed insertion of cut `i`. -/
def step (i : ι) : D.Total →ₗ[ℂ] D.Total where
  toFun x s := if i ∈ s then sign s i • D.map (Finset.erase_subset i s) (x (s.erase i)) else 0
  map_add' x y := by
    funext s
    by_cases hi : i ∈ s <;> simp [hi, map_add, smul_add]
  map_smul' a x := by
    funext s
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte, Pi.smul_apply, map_smul, RingHom.id_apply]
      exact smul_comm _ _ _
    · simp [hi]

@[simp]
theorem step_apply (i : ι) (x : D.Total) (s : Finset ι) :
    D.step i x s =
      if i ∈ s then sign s i • D.map (Finset.erase_subset i s) (x (s.erase i)) else 0 := rfl

theorem step_square (i : ι) (x : D.Total) : D.step i (D.step i x) = 0 := by
  funext s
  by_cases hi : i ∈ s <;> simp [hi]

theorem step_pair (i j : ι) (x : D.Total) :
    D.step i (D.step j x) + D.step j (D.step i x) = 0 := by
  by_cases hne : i = j
  · subst j
    simp [D.step_square]
  funext s
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · have hji : j ≠ i := Ne.symm hne
      simp only [Pi.add_apply, step_apply, hi, hj, Finset.mem_erase, and_true,
        ↓reduceIte, Pi.zero_apply]
      rw [ite_eq_left hji, ite_eq_left hne]
      simp only [map_smul, D.map_map, smul_smul]
      rw [D.map_apply_congr (Finset.erase_right_comm (a := i) (b := j)) _
        ((Finset.erase_subset i (s.erase j)).trans (Finset.erase_subset j s)) x]
      rw [sign_pair hi hj hne, neg_smul, neg_add_cancel]
    · simp [hi, hj]
  · simp [hi]

/-- The degree `k` term, a finite product over sets of exactly `k` cuts. -/
abbrev Degree (k : ℕ) := ∀ s : {s : Finset ι // s.card = k}, D.Obj s.1

/-- Extend a homogeneous family by zero. -/
def extend (k : ℕ) : D.Degree k →ₗ[ℂ] D.Total where
  toFun x s := if h : s.card = k then x ⟨s, h⟩ else 0
  map_add' x y := by
    funext s
    by_cases h : s.card = k <;> simp [h]
  map_smul' a x := by
    funext s
    by_cases h : s.card = k <;> simp [h]

/-- Restrict a total family to its homogeneous degree. -/
def restrict (k : ℕ) : D.Total →ₗ[ℂ] D.Degree k where
  toFun x s := x s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem extend_apply (k : ℕ) (x : D.Degree k) (s : Finset ι) :
    D.extend k x s = if h : s.card = k then x ⟨s, h⟩ else 0 := rfl

@[simp]
theorem restrict_apply (k : ℕ) (x : D.Total) (s : {s : Finset ι // s.card = k}) :
    D.restrict k x s = x s.1 := rfl

@[simp]
theorem restrict_extend (k : ℕ) (x : D.Degree k) : D.restrict k (D.extend k x) = x := by
  funext s
  simp [s.property]

theorem extend_injective (k : ℕ) : Function.Injective (D.extend k) := by
  intro x y h
  simpa using congrArg (D.restrict k) h

variable [Fintype ι]

/-- The alternating differential, summing all elementary cut insertions. -/
def differential : D.Total →ₗ[ℂ] D.Total := ∑ i, D.step i

@[simp]
theorem differential_apply (x : D.Total) : D.differential x = ∑ i, D.step i x := by
  simp [differential]

/-- Cancellation pairs the two possible orders of insertion of distinct cuts. -/
theorem differential_square (x : D.Total) : D.differential (D.differential x) = 0 := by
  simp only [differential_apply, map_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    exact D.step_pair p.2 p.1 x
  · intro p _ hnonzero hfixed
    have heq : p.1 = p.2 := by simpa using congrArg Prod.fst hfixed.symm
    exact hnonzero (by simp [heq, D.step_square])
  · intro p _
    simp
  · intro p _
    simp

theorem differential_vanishes_off_degree (k : ℕ) (x : D.Total)
    (hx : ∀ s, s.card ≠ k → x s = 0) (s : Finset ι) (hs : s.card ≠ k + 1) :
    D.differential x s = 0 := by
  rw [differential_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ s
  · have hcard := Finset.card_erase_add_one hi
    have hne : (s.erase i).card ≠ k := by omega
    simp [hi, hx _ hne]
  · simp [hi]

/-- The degree-raising signed differential. -/
def degreeDifferential (k : ℕ) : D.Degree k →ₗ[ℂ] D.Degree (k + 1) :=
  D.restrict (k + 1) ∘ₗ D.differential ∘ₗ D.extend k

theorem extend_degreeDifferential (k : ℕ) (x : D.Degree k) :
    D.extend (k + 1) (D.degreeDifferential k x) = D.differential (D.extend k x) := by
  funext s
  by_cases hs : s.card = k + 1
  · simp [hs, degreeDifferential]
  · rw [extend_apply, dite_eq_right hs]
    symm
    apply D.differential_vanishes_off_degree k (D.extend k x) _ s hs
    intro t ht
    simp [ht]

theorem degreeDifferential_square (k : ℕ) (x : D.Degree k) :
    D.degreeDifferential (k + 1) (D.degreeDifferential k x) = 0 := by
  apply D.extend_injective (k + 1 + 1)
  rw [D.extend_degreeDifferential, D.extend_degreeDifferential,
    D.differential_square, map_zero]

end Diagram
end Langlands.Aubert.CutComplex
