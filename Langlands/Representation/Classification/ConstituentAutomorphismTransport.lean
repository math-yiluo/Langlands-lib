import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! Strong constituent relations under pullback by group automorphisms. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

variable {G : Type uG} [Group G]
  {V W : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {π : Representation ℂ G W}

/-- Pullback along an automorphism preserves a strong socle and its image. -/
theorem IsIrreducibleSocle.comp_mulEquiv (h : IsIrreducibleSocle ρ π)
    (e : G ≃* G) :
    IsIrreducibleSocle (ρ.comp e.toMonoidHom) (π.comp e.toMonoidHom) := by
  obtain ⟨hi, j, hj, hu⟩ := h
  let jθ : Representation.IntertwiningMap (π.comp e.toMonoidHom)
      (ρ.comp e.toMonoidHom) :=
    ⟨j.toLinearMap, fun g => j.isIntertwining' (e g)⟩
  refine ⟨(CuspidalSupport.isIrreducible_comp_mulEquiv_iff π e).mpr hi,
    jθ, hj, ?_⟩
  intro W' _ _ π' hi' j' hj'
  let j₀ : Representation.IntertwiningMap (π'.comp e.symm.toMonoidHom) ρ :=
    ⟨j'.toLinearMap, fun g => by
      have hg := j'.isIntertwining' (e.symm g)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] using hg⟩
  exact hu W' (π'.comp e.symm.toMonoidHom)
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff π' e.symm).mpr hi') j₀ hj'

/-- Pullback along an automorphism preserves a strong head and its kernel. -/
theorem IsIrreducibleHead.comp_mulEquiv (h : IsIrreducibleHead ρ π)
    (e : G ≃* G) :
    IsIrreducibleHead (ρ.comp e.toMonoidHom) (π.comp e.toMonoidHom) := by
  obtain ⟨hi, q, hq, hu⟩ := h
  let qθ : Representation.IntertwiningMap (ρ.comp e.toMonoidHom)
      (π.comp e.toMonoidHom) :=
    ⟨q.toLinearMap, fun g => q.isIntertwining' (e g)⟩
  refine ⟨(CuspidalSupport.isIrreducible_comp_mulEquiv_iff π e).mpr hi,
    qθ, hq, ?_⟩
  intro W' _ _ π' hi' q' hq'
  let q₀ : ρ.IntertwiningMap (π'.comp e.symm.toMonoidHom) :=
    ⟨q'.toLinearMap, fun g => by
      have hg := q'.isIntertwining' (e.symm g)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply] using hg⟩
  exact hu W' (π'.comp e.symm.toMonoidHom)
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff π' e.symm).mpr hi') q₀ hq'

end Langlands.Classification
