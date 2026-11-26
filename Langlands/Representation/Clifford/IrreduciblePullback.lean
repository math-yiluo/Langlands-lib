import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Basic

/-! # Pullbacks and intertwiners of irreducible representations -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uV uW

variable {K : Type*} [Group K] {L : Type*} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Irreducibility of a precomposition implies irreducibility. -/
theorem isIrreducible_of_comp (ρ : Representation ℂ L V) (c : K →* L)
    (h : Representation.IsIrreducible (ρ.comp c)) : ρ.IsIrreducible := by
  let := h
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro he
    have hbt : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top (α := Subrepresentation (ρ.comp c))
      (Subrepresentation.toSubmodule_injective hbt)
  refine { exists_pair_ne := ⟨⊥, ⊤, hbot⟩, eq_bot_or_eq_top := fun W => ?_ }
  let W' : Subrepresentation (ρ.comp c) :=
    ⟨W.toSubmodule, fun k _ hv => W.apply_mem_toSubmodule (c k) hv⟩
  rcases h.eq_bot_or_eq_top W' with h' | h'
  · have h'' := congrArg Subrepresentation.toSubmodule h'
    exact Or.inl (Subrepresentation.toSubmodule_injective h'')
  · have h'' := congrArg Subrepresentation.toSubmodule h'
    exact Or.inr (Subrepresentation.toSubmodule_injective h'')

variable {J : Type*} [Group J]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A nonzero intertwiner between irreducible representations is an equivalence. -/
theorem nonempty_equiv_of_ne_zero (ρ : Representation ℂ J V) (σ : Representation ℂ J W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (T : ρ.IntertwiningMap σ) (hT : T ≠ 0) :
    Nonempty (ρ.Equiv σ) := by
  let := hρ
  let := hσ
  exact ⟨T.ofBijective ((IsIrreducible.bijective_or_eq_zero T).resolve_right hT)⟩

end Langlands.FiniteRepresentation.SplitDegree
