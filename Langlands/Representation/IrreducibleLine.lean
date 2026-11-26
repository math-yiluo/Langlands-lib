import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.IntervalCases

namespace Representation

/-- A one-dimensional complex representation is irreducible. -/
theorem isIrreducible_of_complex_finrank_eq_one {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (h : Module.finrank ℂ V = 1) : ρ.IsIrreducible := by
  have : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ h
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤)
    (congrArg Subrepresentation.toSubmodule h')⟩, eq_bot_or_eq_top := fun U => ?_ }
  have hle : Module.finrank ℂ U.toSubmodule ≤ 1 := h ▸ Submodule.finrank_le _
  interval_cases hU : Module.finrank ℂ U.toSubmodule
  · left
    exact Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp hU)
  · right
    exact Subrepresentation.toSubmodule_injective
      (Submodule.eq_top_of_finrank_eq (hU.trans h.symm))

end Representation
