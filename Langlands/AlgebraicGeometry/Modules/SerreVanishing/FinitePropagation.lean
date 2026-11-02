import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic

/-! # Finite generation and propagation for the two-bundle Serre argument -/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.Modules.SerrePropagation

/-- Pointwise eventual annihilation in a sequence of modules is uniform on a
finitely generated starting module. -/
theorem finiteModule_eventually_zero_map
    {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)
    [Module.Finite R (F.obj 0)]
    (hkill : ∀ x : F.obj 0, ∃ n : ℕ,
      (F.map (homOfLE (Nat.zero_le n))).hom x = 0) :
    ∃ n : ℕ, F.map (homOfLE (Nat.zero_le n)) = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Module.finite_def.mp
    (inferInstance : Module.Finite R (F.obj 0)))
  choose n hn using hkill
  let N := s.sup n
  refine ⟨N, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hker : (⊤ : Submodule R (F.obj 0)) ≤
      (F.map (homOfLE (Nat.zero_le N))).hom.ker := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro y hy
    have hy' : y ∈ s := hy
    have hle : n y ≤ N := Finset.le_sup hy'
    have hcomp : F.map (homOfLE (Nat.zero_le N)) =
        F.map (homOfLE (Nat.zero_le (n y))) ≫ F.map (homOfLE hle) := by
      rw [← F.map_comp]
      rfl
    change (F.map (homOfLE (Nat.zero_le N))).hom y = 0
    rw [hcomp]
    simp [hn y]
  exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule R (F.obj 0)))

/-- A sequence with a finitely generated initial module, surjective transition
maps and pointwise eventual annihilation eventually reaches a zero module. -/
theorem finiteModule_surjective_sequence_eventually_isZero
    {R : Type u} [Ring R] (F : ℕ ⥤ ModuleCat.{v} R)
    [Module.Finite R (F.obj 0)]
    (hsurj : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n))).hom)
    (hkill : ∀ x : F.obj 0, ∃ n : ℕ,
      (F.map (homOfLE (Nat.zero_le n))).hom x = 0) :
    ∃ n : ℕ, IsZero (F.obj n) := by
  have hsurj' : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.zero_le n))).hom := by
    intro n
    induction n with
    | zero =>
        simpa using (Function.surjective_id : Function.Surjective (id : F.obj 0 → F.obj 0))
    | succ n ih =>
        have hcomp : F.map (homOfLE (Nat.zero_le (n + 1))) =
            F.map (homOfLE (Nat.zero_le n)) ≫ F.map (homOfLE (Nat.le_succ n)) := by
          rw [← F.map_comp]
          rfl
        rw [hcomp]
        exact (hsurj n).comp ih
  obtain ⟨n, hn⟩ := finiteModule_eventually_zero_map F hkill
  refine ⟨n, ModuleCat.isZero_iff_subsingleton.mpr ?_⟩
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨x, rfl⟩ := hsurj' n y
  simp [hn]

/-- Positive-step closure propagates a predicate along the associated grid. -/
theorem quadrant_grid
    (P : ℕ → ℕ → Prop) (m d₁ d₂ : ℕ)
    (h₁ : ∀ a b, m ≤ a → m ≤ b → P a b → P (a + d₁) b)
    (h₂ : ∀ a b, m ≤ a → m ≤ b → P a b → P a (b + d₂))
    {a b : ℕ} (ha : m ≤ a) (hb : m ≤ b) (h : P a b) :
    ∀ k l : ℕ, P (a + k * d₁) (b + l * d₂) := by
  have hx : ∀ k : ℕ, P (a + k * d₁) b := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
        simpa [Nat.succ_mul, Nat.add_assoc] using
          h₁ (a + k * d₁) b (by omega) hb ih
  intro k l
  induction l with
  | zero => simpa using hx k
  | succ l ih =>
      simpa [Nat.succ_mul, Nat.add_assoc] using
        h₂ (a + k * d₁) (b + l * d₂) (by omega) (by omega) ih

/-- Finitely many positive degrees and residue-class seeds give a single
quadrant threshold. This is the numerical step of the two-bundle argument. -/
theorem exists_uniform_quadrant
    (P : ℕ → ℕ → ℕ → Prop) (m d₁ d₂ D : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h₁ : ∀ i, 0 < i → ∀ a b, m ≤ a → m ≤ b → P i a b → P i (a + d₁) b)
    (h₂ : ∀ i, 0 < i → ∀ a b, m ≤ a → m ≤ b → P i a b → P i a (b + d₂))
    (hdegree : ∀ i a b, D < i → P i a b)
    (hseed : ∀ i, 0 < i → i ≤ D → ∀ r₁, r₁ < d₁ → ∀ r₂, r₂ < d₂ →
      ∃ t : ℕ, P i (m + r₁ + t * d₁) (m + r₂)) :
    ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      ∀ i : ℕ, 0 < i → P i a b := by
  classical
  let I := Fin (D + 1) × Fin d₁ × Fin d₂
  have hseed' : ∀ z : I, ∃ t : ℕ, 0 < z.1.val →
      P z.1.val (m + z.2.1.val + t * d₁) (m + z.2.2.val) := by
    intro z
    by_cases hz : 0 < z.1.val
    · obtain ⟨t, ht⟩ := hseed z.1.val hz (by omega)
        z.2.1.val z.2.1.isLt z.2.2.val z.2.2.isLt
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => (hz h).elim⟩
  choose t ht using hseed'
  let T := Finset.univ.sup t
  refine ⟨m + T * d₁, ?_⟩
  intro a b ha hb i hi
  by_cases hiD : i ≤ D
  · let r₁ := (a - m) % d₁
    let r₂ := (b - m) % d₂
    let q₁ := (a - m) / d₁
    let q₂ := (b - m) / d₂
    let z : I := (⟨i, by omega⟩,
      ⟨r₁, Nat.mod_lt _ hd₁⟩, ⟨r₂, Nat.mod_lt _ hd₂⟩)
    have htT : t z ≤ T := Finset.le_sup (Finset.mem_univ z)
    have hTq : T ≤ q₁ := by
      apply (Nat.le_div_iff_mul_le hd₁).mpr
      omega
    have hseedz : P i (m + r₁ + t z * d₁) (m + r₂) := ht z hi
    have hgrid := quadrant_grid (P i) m d₁ d₂ (h₁ i hi) (h₂ i hi)
      (a := m + r₁ + t z * d₁) (b := m + r₂)
      (by omega) (by omega) hseedz (q₁ - t z) q₂
    have ha' : m + r₁ + t z * d₁ + (q₁ - t z) * d₁ = a := by
      have hdiv := Nat.mod_add_div (a - m) d₁
      have htq : t z ≤ q₁ := htT.trans hTq
      have hmul : t z * d₁ + (q₁ - t z) * d₁ = q₁ * d₁ := by
        rw [← Nat.add_mul, Nat.add_sub_of_le htq]
      rw [Nat.add_assoc (m + r₁), hmul]
      dsimp [r₁, q₁]
      have hma : m ≤ a := by omega
      nlinarith [Nat.sub_add_cancel hma]
    have hb' : m + r₂ + q₂ * d₂ = b := by
      have hdiv := Nat.mod_add_div (b - m) d₂
      dsimp [r₂, q₂]
      have hmb : m ≤ b := by omega
      nlinarith [Nat.sub_add_cancel hmb]
    simpa only [ha', hb'] using hgrid
  · exact hdegree i a b (by omega)

end Langlands.AlgebraicGeometry.Modules.SerrePropagation
