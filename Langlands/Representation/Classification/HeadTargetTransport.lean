import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! Target transport of the actual strong irreducible head relation. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

variable {G : Type uG} [Group G]
  {V W W' : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {π : Representation ℂ G W}
  {π' : Representation ℂ G W'}

/-- A target equivalence preserves a strong irreducible head, including its
uniqueness as a quotient object. -/
theorem IsIrreducibleHead.of_targetEquiv (h : IsIrreducibleHead ρ π)
    (e : π.Equiv π') : IsIrreducibleHead ρ π' := by
  obtain ⟨hπ, q, hq, hu⟩ := h
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp hπ,
    e.toIntertwiningMap.comp q, e.surjective.comp hq, ?_⟩
  intro W'' _ _ σ hσ q' hq'
  rw [hu W'' σ hσ q' hq']
  ext v
  simp only [LinearMap.mem_ker]
  exact (map_eq_zero_iff e e.injective).symm

end Langlands.Classification
