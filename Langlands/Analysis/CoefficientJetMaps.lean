import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Continuous coefficient maps on finite jets -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.CoefficientJetMaps

universe u v w

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [ContinuousAdd F]
  {H : Type w} [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [ContinuousAdd H]

/-- A sequence of continuous linear coefficient operators acts on jets by truncated
power-series multiplication. -/
def jetMap (m : ℕ) (T : ℕ → E →L[ℂ] F) : (Fin m → E) →L[ℂ] (Fin m → F) :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin m,
    if j.val ≤ i.val then (T (i.val - j.val)).comp (ContinuousLinearMap.proj (R := ℂ) j) else 0

theorem jetMap_apply {m : ℕ} (T : ℕ → E →L[ℂ] F) (x : Fin m → E) (i : Fin m) :
    jetMap m T x i = ∑ j : Fin m, if j.val ≤ i.val then T (i.val - j.val) (x j) else 0 := by
  simp only [jetMap, ContinuousLinearMap.pi_apply, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem jetMap_single_apply {m : ℕ} (T : ℕ → E →L[ℂ] F) (j i : Fin m) (x : E) :
    jetMap m T (Pi.single j x) i = if j.val ≤ i.val then T (i.val - j.val) x else 0 := by
  rw [jetMap_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

/-- A single nonzero coefficient acts by shifting the input series and applying that coefficient. -/
theorem jetMap_monomial_apply {m : ℕ} (k : ℕ) (L : E →L[ℂ] F) (x : Fin m → E) (i : Fin m) :
    jetMap m (fun d => if d = k then L else 0) x i =
      if hk : k ≤ i.val then L (x ⟨i.val - k, by omega⟩) else 0 := by
  rw [jetMap_apply]
  by_cases hk : k ≤ i.val
  · let j : Fin m := ⟨i.val - k, by omega⟩
    rw [dite_eq_left hk, Finset.sum_eq_single j]
    · have hj : j.val ≤ i.val := by dsimp [j]; omega
      have he : i.val - j.val = k := by dsimp [j]; omega
      rw [ite_eq_left hj, ite_eq_left he]
    · intro a _ ha
      by_cases hai : a.val ≤ i.val
      · have hne : i.val - a.val ≠ k := by
          intro h
          apply ha
          apply Fin.ext
          dsimp [j]
          omega
        simp [hai, hne]
      · simp [hai]
    · simp
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro a _
    have hne : i.val - a.val ≠ k := by omega
    by_cases ha : a.val ≤ i.val <;> simp [ha, hne]

omit [Module ℂ H] [TopologicalSpace H] [ContinuousAdd H] in
private theorem reindex_between {m : ℕ} (j i : Fin m) (hji : j.val ≤ i.val) (f : ℕ → H) :
    (∑ l ∈ (Finset.univ.filter fun l : Fin m => j.val ≤ l.val ∧ l.val ≤ i.val), f (l.val - j.val)) =
      ∑ a ∈ Finset.range (i.val - j.val + 1), f a := by
  apply Finset.sum_bij (fun l _ => l.val - j.val)
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2
    exact Finset.mem_range.mpr (by omega)
  · intro l hl k hk h
    have hl' := (Finset.mem_filter.mp hl).2
    have hk' := (Finset.mem_filter.mp hk).2
    exact Fin.ext (by omega)
  · intro a ha
    have h := Finset.mem_range.mp ha
    have hm := i.isLt
    let l : Fin m := ⟨a + j.val, by omega⟩
    refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · dsimp [l]
      omega
    · dsimp [l]
      omega
  · intro l _
    rfl

private theorem composite_single {m : ℕ}
    (T : ℕ → E →L[ℂ] F) (U : ℕ → F →L[ℂ] H) (V : ℕ → E →L[ℂ] H)
    (h : ∀ d x, (∑ a ∈ Finset.range (d + 1), U (d - a) (T a x)) = V d x)
    (j i : Fin m) (x : E) :
    jetMap m U (jetMap m T (Pi.single j x)) i = jetMap m V (Pi.single j x) i := by
  rw [jetMap_apply, jetMap_single_apply V]
  simp_rw [jetMap_single_apply T]
  have hsum :
      (∑ l : Fin m, if l.val ≤ i.val then
        U (i.val - l.val) (if j.val ≤ l.val then T (l.val - j.val) x else 0) else 0) =
      ∑ l ∈ (Finset.univ.filter fun l : Fin m => j.val ≤ l.val ∧ l.val ≤ i.val),
        U (i.val - l.val) (T (l.val - j.val) x) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hi : l.val ≤ i.val <;> by_cases hj : j.val ≤ l.val <;> simp [hi, hj]
  rw [hsum]
  by_cases hji : j.val ≤ i.val
  · rw [ite_eq_left hji, ← h]
    calc
      _ = ∑ l ∈ (Finset.univ.filter fun l : Fin m => j.val ≤ l.val ∧ l.val ≤ i.val),
          U (i.val - j.val - (l.val - j.val)) (T (l.val - j.val) x) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [show i.val - j.val - (l.val - j.val) = i.val - l.val by
          have h := (Finset.mem_filter.mp hl).2
          omega]
      _ = _ := reindex_between j i hji (fun a => U (i.val - j.val - a) (T a x))
  · rw [ite_eq_right hji]
    apply Finset.sum_eq_zero
    intro l hl
    have hh := (Finset.mem_filter.mp hl).2
    omega

/-- Composition of continuous jet maps is the jet map of the coefficient convolution. -/
def CoefficientJetCompositionStatement : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (F : Type v) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [ContinuousAdd F]
    (H : Type w) [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [ContinuousAdd H]
    (T : ℕ → E →L[ℂ] F) (U : ℕ → F →L[ℂ] H) (V : ℕ → E →L[ℂ] H),
    (∀ d x, (∑ a ∈ Finset.range (d + 1), U (d - a) (T a x)) = V d x) →
    ∀ m, (jetMap m U).comp (jetMap m T) = jetMap m V

theorem coefficientJetComposition : CoefficientJetCompositionStatement.{u, v, w} := by
  intro E _ _ _ F _ _ _ _ H _ _ _ _ T U V h m
  apply ContinuousLinearMap.ext
  intro x
  have he : x = ∑ j : Fin m, Pi.single j (x j) := (LinearMap.sum_single_apply (fun _ : Fin m => E) x).symm
  conv_lhs => rw [he]
  conv_rhs => rw [he]
  simp only [map_sum, ContinuousLinearMap.comp_apply]
  exact Finset.sum_congr rfl fun j _ => funext fun i => composite_single T U V h j i (x j)

end Langlands.Analysis.CoefficientJetMaps
