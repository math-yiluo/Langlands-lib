import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Analysis.Complex.Basic

/-! # Invariant subspaces under a covariant linear equivalence -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

/-- Image and preimage identify invariant subspaces under conjugated actions. -/
def conjugatedSubrepresentationOrderIso
    {A V W : Type*} [Monoid A] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ A V) (τ : Representation ℂ A W)
    (α : A ≃* A) (e : V ≃ₗ[ℂ] W)
    (hc : ∀ a f, τ a (e f) = e (ρ (α a) f)) :
    Subrepresentation ρ ≃o Subrepresentation τ where
  toFun P :=
    { toSubmodule := P.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule a _ hf := by
        change ∃ f, f ∈ P.toSubmodule ∧ e f = _ at hf
        obtain ⟨f, hf, rfl⟩ := hf
        rw [hc]
        exact Submodule.mem_map_of_mem (P.apply_mem_toSubmodule (α a) hf) }
  invFun Q :=
    { toSubmodule := Q.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule a f hf := by
        change e (ρ a f) ∈ Q
        have hcov := hc (α.symm a) f
        rw [α.apply_symm_apply] at hcov
        rw [← hcov]
        exact Q.apply_mem_toSubmodule (α.symm a) hf }
  left_inv P := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).symm_apply_apply P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    ((Submodule.orderIsoMapComap e).apply_symm_apply Q.toSubmodule)
  map_rel_iff' := (Submodule.orderIsoMapComap e).map_rel_iff

end Langlands
