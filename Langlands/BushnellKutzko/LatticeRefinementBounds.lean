import Langlands.BushnellKutzko.UnitFiltration
import Mathlib.Order.Int.LeastGreatest

/-! # Unit-group bounds for refinement of a lattice chain -/

noncomputable section

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uF uV

variable {O : Type uO} [CommRing O] {F : Type uF} [Field F] [Algebra O F]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
  {L M : LatticeChain O F V}

private theorem exists_between_of_strictMono {c : ℤ → ℤ} (hc : StrictMono c) (i : ℤ) :
    ∃ j, c j ≤ i ∧ i < c (j + 1) := by
  have hm : Monotone (fun j => c j - j) := monotone_int_of_le_succ fun j => by
    have h : c j < c (j + 1) := hc (by omega)
    omega
  have hbdd : ∃ b, ∀ j, c j ≤ i → j ≤ b := by
    refine ⟨max 0 (i - c 0), fun j hj => ?_⟩
    by_cases h : 0 ≤ j
    · have h' : c 0 - 0 ≤ c j - j := hm h
      exact le_max_of_le_right (by omega)
    · exact le_max_of_le_left (by omega)
  have hne : ∃ j, c j ≤ i := by
    let j := min 0 (i - c 0)
    have h₀ : j ≤ 0 := min_le_left _ _
    have hi : j ≤ i - c 0 := min_le_right _ _
    have h' : c j - j ≤ c 0 - 0 := hm h₀
    exact ⟨j, by omega⟩
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨j, hj, lt_of_not_ge fun h => ?_⟩
  have := hmax (j + 1) h
  omega

/-- A refinement gives a smaller order and a larger depth-one filtration
lattice. The latter follows by locating each position between retained
lattices. -/
theorem refinement_order_endFiltration_bounds (h : ∀ i, ∃ j, M.lattice j = L.lattice i) :
    M.order ≤ L.order ∧ L.endFiltration 1 ≤ M.endFiltration 1 := by
  classical
  choose c hc using h
  have hs : StrictMono c := by
    intro i j hij
    by_contra! hn
    have hL : L.lattice i ≤ L.lattice j := by
      rw [← hc i, ← hc j]
      exact M.antitone hn
    exact (L.strictAnti hij).not_ge hL
  constructor
  · intro x hx
    apply L.mem_order.mpr
    intro i v hv
    rw [← hc i] at hv ⊢
    exact (M.mem_order.mp hx) (c i) v hv
  · intro x hx i v hv
    obtain ⟨j, hj, hj'⟩ := exists_between_of_strictMono hs i
    have hv' : v ∈ L.lattice j := hc j ▸ M.antitone hj hv
    have hx' : x v ∈ M.lattice (c (j + 1)) := hc (j + 1) ▸ hx j v hv'
    exact M.antitone (by omega) hx'

/-- In a refinement, the depth-zero units become a subgroup and the depth-one
units contain the original depth-one units. -/
theorem refinement_unitFiltration_bounds (h : ∀ i, ∃ j, M.lattice j = L.lattice i) :
    M.unitFiltration 0 ≤ L.unitFiltration 0 ∧ L.unitFiltration 1 ≤ M.unitFiltration 1 := by
  obtain ⟨horder, h₁⟩ := refinement_order_endFiltration_bounds h
  constructor
  · intro g hg
    exact (L.mem_unitFiltration_zero).mpr ⟨horder hg.1, horder hg.2.1⟩
  · intro g hg
    obtain ⟨u, hu, heq⟩ := M.exists_mem_unitFiltration (n := 1) le_rfl (h₁ hg.2.2)
    have hug : u = g := Units.ext (by rw [heq]; abel)
    exact hug ▸ hu

end Langlands.BushnellKutzko.LatticeChain
