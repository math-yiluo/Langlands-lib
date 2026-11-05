import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Stable flags for nilpotent families of endomorphisms

Authors: Worker 1429
-/

noncomputable section

open Module LieModule

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Langlands.Algebra

/-- Let `A` be a bracket-closed subspace of `End V` consisting of nilpotent endomorphisms, and `S`
a set of endomorphisms normalizing `A`. Then there is a finite descending flag of subspaces of `V`
from `⊤` to `⊥` such that `A` maps each step into the next and `S` preserves each step. -/
theorem exists_stable_flag_of_isNilpotent
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : Submodule k (Module.End k V))
    (hlie : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ A)
    (hnil : ∀ a ∈ A, IsNilpotent a)
    (S : Set (Module.End k V)) (hS : ∀ g ∈ S, ∀ a ∈ A, ⁅g, a⁆ ∈ A) :
    ∃ (F : ℕ → Submodule k V) (m : ℕ), Antitone F ∧ F 0 = ⊤ ∧ F m = ⊥ ∧
      (∀ t, ∀ a ∈ A, ∀ v ∈ F t, a v ∈ F (t + 1)) ∧
      (∀ t, ∀ g ∈ S, ∀ v ∈ F t, g v ∈ F t) := by
  let L : LieSubalgebra k (Module.End k V) :=
    { A with lie_mem' := fun {a b} ha hb => hlie a ha b hb }
  have hmemL : ∀ a, a ∈ L ↔ a ∈ A := fun _ => Iff.rfl
  have htoEnd : ∀ x : L, toEnd k L V x = (x : Module.End k V) := fun _ => rfl
  -- Engel's theorem: `V` is a nilpotent `L`-module.
  have hV : LieModule.IsNilpotent L V := by
    rw [LieModule.isNilpotent_iff_forall' (R := k)]
    intro x
    rw [htoEnd]
    exact hnil x ((hmemL x).mp x.2)
  obtain ⟨m, hm⟩ := (LieModule.isNilpotent_iff k L V).mp hV
  let F : ℕ → Submodule k V := fun t => (lowerCentralSeries k L V t).toSubmodule
  have hstep : ∀ t, ∀ a ∈ A, ∀ v ∈ F t, a v ∈ F (t + 1) := by
    intro t a ha v hv
    change ⁅(⟨a, (hmemL a).mpr ha⟩ : L), v⁆ ∈ lowerCentralSeries k L V (t + 1)
    rw [lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hv
  refine ⟨F, m, ?_, ?_, ?_, hstep, ?_⟩
  · intro s t hst
    exact fun v hv => antitone_lowerCentralSeries k L V hst hv
  · simp [F]
  · simp [F, hm]
  · intro t
    induction t with
    | zero => intro g _ v _; simp [F]
    | succ t ih =>
      intro g hg v hv
      have hspan : F (t + 1) = Submodule.span k
          {x | ∃ (a : L) (n : lowerCentralSeries k L V t), ⁅(a : Module.End k V), (n : V)⁆ = x} := by
        change (lowerCentralSeries k L V (t + 1)).toSubmodule = _
        rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
        apply congrArg
        ext x
        constructor
        · rintro ⟨⟨a, -⟩, n, rfl⟩
          exact ⟨a, n, rfl⟩
        · rintro ⟨a, n, rfl⟩
          exact ⟨⟨a, LieSubmodule.mem_top a⟩, n, rfl⟩
      have hle : F (t + 1) ≤ (F (t + 1)).comap g := by
        rw [hspan, Submodule.span_le]
        rintro _ ⟨a, n, rfl⟩
        rw [← hspan]
        change g ((a : Module.End k V) (n : V)) ∈ F (t + 1)
        have hga : ⁅g, (a : Module.End k V)⁆ ∈ A := hS g hg a ((hmemL a).mp a.2)
        have hcomm : g ((a : Module.End k V) (n : V)) =
            (a : Module.End k V) (g n) + ⁅g, (a : Module.End k V)⁆ n := by
          have h0 : (⁅g, (a : Module.End k V)⁆ : Module.End k V) n =
              g ((a : Module.End k V) n) - (a : Module.End k V) (g n) := rfl
          rw [h0]
          abel
        rw [hcomm]
        exact (F (t + 1)).add_mem (hstep t a ((hmemL a).mp a.2) _ (ih g hg n n.2))
          (hstep t _ hga n n.2)
      exact hle hv

end Langlands.Algebra
