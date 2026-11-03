import Langlands.Algebra.FiniteChamberLatticeStatement
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! # Finite orthant coordinates by Euclidean division -/

namespace Langlands

open scoped BigOperators

theorem finiteChamberLattice.{uΔ, uX} :
    FiniteChamberLatticeStatement.{uΔ, uX} := by
  intro Δ _ X _ pair hstd
  classical
  have hex (α : Δ) : ∃ g : X,
      0 < pair α g ∧ ∀ β, β ≠ α → pair β g = 0 := by
    obtain ⟨g, hgzero, hgpos⟩ := hstd (Finset.univ.erase α)
    refine ⟨g, hgpos α (by simp), fun β hβα => ?_⟩
    exact hgzero β (by simp [hβα])
  choose gen hgenpos hgenzero using hex
  refine ⟨gen, hgenpos, hgenzero, fun B => ?_⟩
  let d : Δ → ℤ := fun α => pair α (gen α)
  let φ : X → (Δ → ℤ) := fun x α => pair α x
  let S : Set X := {x | ∀ α, -B ≤ pair α x ∧ pair α x ≤ d α - B}
  have hbox : (φ '' S).Finite := by
    refine (Set.Finite.pi (t := fun α : Δ => Set.Icc (-B) (d α - B))
      fun α => Set.finite_Icc _ _).subset ?_
    rintro _ ⟨x, hx, rfl⟩ α _
    exact hx α
  refine ⟨Function.invFunOn φ S '' (φ '' S), hbox.image _, fun x hx => ?_⟩
  let n : Δ → ℕ := fun α => ((pair α x + B) / d α).toNat
  have hn (α : Δ) : (n α : ℤ) = (pair α x + B) / d α := by
    exact Int.natCast_toNat_eq_self.mpr
      (Int.ediv_nonneg (by linarith [hx α]) (hgenpos α).le)
  let s : X := ∑ α, n α • gen α
  have hs (α : Δ) : pair α s = (n α : ℤ) * d α := by
    dsimp [s]
    simp only [map_sum, map_nsmul, nsmul_eq_mul]
    apply Finset.sum_eq_single α
    · intro β _ hβα
      rw [hgenzero β α (Ne.symm hβα), mul_zero]
    · simp
  let y : X := x - s
  have hy : y ∈ S := by
    intro α
    have heq : pair α y = (pair α x + B) % d α - B := by
      dsimp [y]
      rw [map_sub, hs, hn]
      linarith [Int.emod_add_ediv_mul (pair α x + B) (d α)]
    rw [heq]
    have hpos : 0 < d α := hgenpos α
    constructor
    · linarith [Int.emod_nonneg (pair α x + B) (ne_of_gt hpos)]
    · linarith [Int.emod_lt_of_pos (pair α x + B) hpos]
  let r : X := Function.invFunOn φ S (φ y)
  have hr : r ∈ Function.invFunOn φ S '' (φ '' S) :=
    ⟨φ y, ⟨y, hy, rfl⟩, rfl⟩
  have hpair (α : Δ) : pair α r = pair α y :=
    congrFun (Function.invFunOn_eq (f := φ) (s := S) ⟨y, hy, rfl⟩) α
  refine ⟨r, hr, n, y - r, fun α => ?_, ?_⟩
  · rw [map_sub, hpair, sub_self]
  · dsimp [y, s]
    abel

end Langlands
