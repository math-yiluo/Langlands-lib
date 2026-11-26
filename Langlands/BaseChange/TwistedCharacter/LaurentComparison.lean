import Langlands.Representation.Plancherel.RationalUnitaryNonvanishing
import Mathlib.Algebra.Polynomial.Roots

/-! # Finite scalar comparisons for regular families -/

noncomputable section

namespace Langlands.BaseChange

/-- If two families agree up to a scalar in a fixed finite set at every point of a
separating family of evaluations, one scalar works in the coefficient domain itself. -/
theorem exists_scalar_of_finite_evaluation_comparisons {k R I X : Type*}
    [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (e : I → R →ₐ[k] k) (he : ∀ r : R, (∀ i, e i r = 0) → r = 0)
    (s : Finset k) (F H : X → R)
    (h : ∀ i, ∃ c ∈ s, ∀ x, e i (F x) = c * e i (H x)) :
    ∃ c ∈ s, ∀ x, F x = c • H x := by
  classical
  by_contra hn
  have hn' : ∀ c : s, ∃ x, F x - (c : k) • H x ≠ 0 := by
    intro c
    by_contra h'
    push Not at h'
    exact hn ⟨c, c.property, fun x => sub_eq_zero.mp (h' x)⟩
  choose x hx using hn'
  let q := ∏ c : s, (F (x c) - (c : k) • H (x c))
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hx c)
  apply hq (he q ?_)
  intro i
  obtain ⟨c, hc, hF⟩ := h i
  let j : s := ⟨c, hc⟩
  simp only [q, map_prod, map_sub, map_smul, smul_eq_mul]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_eq_zero.mpr (hF (x j)))

open Plancherel

/-- A comparison by roots of unity on the unitary torus holds with one root
of unity on the full torus. Here each test is represented by a Laurent polynomial. -/
theorem exists_rootOfUnity_laurent_comparison {n d : ℕ} (hd : 0 < d) {X : Type*}
    (F H : X → AddMonoidAlgebra ℂ (Fin n → ℤ))
    (h : ∀ z : Fin n → Circle, ∃ c : ℂ, c ^ d = 1 ∧ ∀ x,
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) (F x) =
        c * finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) (H x)) :
    ∃ c : ℂ, c ^ d = 1 ∧ ∀ (z : Fin n → ℂˣ) x,
      finiteLaurentEvaluation z (F x) = c * finiteLaurentEvaluation z (H x) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_scalar_of_finite_evaluation_comparisons
    (fun z : Fin n → Circle => finiteLaurentEvaluation (fun i => Circle.toUnits (z i)))
    finiteLaurent_eq_zero_of_eval_unitary (Polynomial.nthRootsFinset d (1 : ℂ)) F H
    (fun z => by
      obtain ⟨c, hc, he⟩ := h z
      exact ⟨c, (Polynomial.mem_nthRootsFinset hd 1).mpr hc, he⟩)
  refine ⟨c, (Polynomial.mem_nthRootsFinset hd 1).mp hc, fun z x => ?_⟩
  rw [hF x, map_smul, smul_eq_mul]

end Langlands.BaseChange
