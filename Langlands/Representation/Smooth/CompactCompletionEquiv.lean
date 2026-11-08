import Langlands.Representation.Smooth.CompactCompletionMaps

/-! # Completion of an intertwining equivalence -/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An intertwining equivalence acts componentwise on the completion. -/
def equiv (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (E : ρ.Equiv σ) :
    completion ρ hρ ≃ₗ[ℂ] completion σ hσ where
  toLinearMap := map hρ hσ E.toIntertwiningMap
  invFun := map hσ hρ E.symm.toIntertwiningMap
  left_inv v := by
    apply Subtype.ext
    funext K
    exact E.symm_apply_apply (v.val K)
  right_inv w := by
    apply Subtype.ext
    funext K
    exact E.apply_symm_apply (w.val K)

@[simp]
theorem equiv_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (E : ρ.Equiv σ)
    (v : completion ρ hρ) (K : CompactOpenSubgroup G) :
    (equiv hρ hσ E v).val K = E (v.val K) :=
  rfl

@[simp]
theorem equiv_symm_apply (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (E : ρ.Equiv σ)
    (w : completion σ hσ) (K : CompactOpenSubgroup G) :
    ((equiv hρ hσ E).symm w).val K = E.symm (w.val K) :=
  rfl

end Langlands.CompactCompletion
