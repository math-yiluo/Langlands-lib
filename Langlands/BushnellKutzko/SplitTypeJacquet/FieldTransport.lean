import Langlands.Representation.FiniteGeneralLinear.Cuspidal

/-! # Transport of block subgroups and cuspidality along a field isomorphism

For a ring isomorphism `ψ : k ≃+* k'` of fields, the entrywise map `GL_n(k) → GL_n(k')` carries
each standard block parabolic and its unipotent radical onto the corresponding subgroups over
`k'`, and composing a cuspidal representation of `GL_n(k)` with the inverse map gives a cuspidal
representation of `GL_n(k')`. -/

noncomputable section

open Langlands.GeneralLinear

namespace Langlands.BushnellKutzko.SplitTypeJacquet

variable {k k' : Type*} [Field k] [Field k'] (ψ : k ≃+* k') {n : ℕ}

/-- The entrywise image of an invertible matrix under a field isomorphism. -/
abbrev glMap : GeneralLinear n k →* GeneralLinear n k' :=
  Matrix.GeneralLinearGroup.map (ψ : k →+* k')

theorem glMap_apply (g : GeneralLinear n k) (a b : Fin n) : glMap ψ g a b = ψ (g a b) := rfl

theorem glMap_symm_glMap (g : GeneralLinear n k) : glMap ψ.symm (glMap ψ g) = g := by
  ext a b
  simp

theorem glMap_glMap_symm (g : GeneralLinear n k') : glMap ψ (glMap ψ.symm g) = g := by
  ext a b
  simp

theorem glMap_mem_parabolic {B : BlockShape n} {g : GeneralLinear n k}
    (hg : g ∈ B.parabolic k) : glMap ψ g ∈ B.parabolic k' := by
  rw [BlockShape.mem_parabolic_iff] at hg ⊢
  intro i j a b hij
  rw [glMap_apply, hg i j a b hij, map_zero]

theorem glMap_mem_unipotentSubgroup {B : BlockShape n} {g : GeneralLinear n k}
    (hg : g ∈ B.unipotentSubgroup k) : glMap ψ g ∈ B.unipotentSubgroup k' := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hg ⊢
  refine ⟨glMap_mem_parabolic ψ hg.1, fun i a b => ?_⟩
  rw [glMap_apply, hg.2 i a b]
  split_ifs <;> simp

include ψ in
theorem parabolic_ne_top_of_map {B : BlockShape n} (h : B.parabolic k' ≠ ⊤) :
    B.parabolic k ≠ ⊤ := by
  intro htop
  apply h
  rw [eq_top_iff]
  intro g _
  rw [← glMap_glMap_symm ψ g]
  exact glMap_mem_parabolic ψ (htop ▸ Subgroup.mem_top _)

/-- **Cuspidality is invariant under a field isomorphism.** -/
theorem isCuspidal_comp_glMap {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GeneralLinear n k) W} (hρ : FiniteGeneralLinear.IsCuspidal ρ) :
    FiniteGeneralLinear.IsCuspidal (ρ.comp (glMap ψ.symm)) := by
  intro B hB v hv
  refine hρ B (parabolic_ne_top_of_map ψ hB) v fun u hu => ?_
  have h := hv (glMap ψ u) (glMap_mem_unipotentSubgroup ψ hu)
  rwa [MonoidHom.comp_apply, glMap_symm_glMap] at h

end Langlands.BushnellKutzko.SplitTypeJacquet
