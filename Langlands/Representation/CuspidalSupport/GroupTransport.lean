import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

namespace Langlands

universe uR uG uH uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module R V]

namespace Jacquet

/-- Pullback subgroup coinvariants are the coinvariants of its actual image. -/
def coinvariantsMapEquiv (ρ : Representation R G V) (f : H →* G) (N : Subgroup H) :
    Coinvariants (ρ.comp f) N ≃ₗ[R] Coinvariants ρ (N.map f) where
  __ := lift (ρ.comp f) N (mk ρ (N.map f)) (fun n => LinearMap.ext fun v =>
    mk_apply_subgroup ρ (N.map f) ⟨f n, ⟨n, n.property, rfl⟩⟩ v)
  invFun := lift ρ (N.map f) (mk (ρ.comp f) N) (fun n => by
    obtain ⟨h, hh, heq⟩ := n.property
    apply LinearMap.ext
    intro v
    change mk (ρ.comp f) N (ρ (n : G) v) = mk (ρ.comp f) N v
    rw [← heq]
    exact mk_apply_subgroup (ρ.comp f) N ⟨h, hh⟩ v)
  left_inv x := by
    obtain ⟨v, rfl⟩ := mk_surjective (ρ.comp f) N x
    rfl
  right_inv x := by
    obtain ⟨v, rfl⟩ := mk_surjective ρ (N.map f) x
    rfl

@[simp]
theorem coinvariantsMapEquiv_mk (ρ : Representation R G V) (f : H →* G)
    (N : Subgroup H) (v : V) :
    coinvariantsMapEquiv ρ f N (mk (ρ.comp f) N v) = mk ρ (N.map f) v := rfl

end Jacquet

/-- Pullback fixed vectors under an equivalence equal fixed vectors for its image subgroup. -/
theorem fixedVectors_comp_mulEquiv (ρ : Representation R G V) (e : H ≃* G)
    (K : Subgroup H) :
    fixedVectors (ρ.comp e.toMonoidHom) K = fixedVectors ρ (K.comap e.symm.toMonoidHom) := by
  ext v
  constructor
  · intro hv
    change ∀ g : K.comap e.symm.toMonoidHom, ρ (g : G) v = v
    intro g
    have h := hv ⟨e.symm g, g.property⟩
    change ρ (e (e.symm g)) v = v at h
    simpa only [MulEquiv.apply_symm_apply] using h
  · intro hv
    change ∀ h : K, ρ (e (h : H)) v = v
    intro h
    exact hv ⟨e h, by simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using h.property⟩

section Topology

variable [TopologicalSpace G] [TopologicalSpace H]

/-- Admissibility pulls back through a continuous group equivalence. -/
theorem isAdmissible_comp_continuousMulEquiv (ρ : Representation R G V) (e : H ≃ₜ* G)
    (hρ : IsAdmissible ρ) : IsAdmissible (ρ.comp e.toMonoidHom) := by
  refine ⟨isSmooth_comp e.toMonoidHom e.continuous hρ.1, ?_⟩
  intro K
  rw [fixedVectors_comp_mulEquiv ρ e.toMulEquiv K.toSubgroup]
  exact hρ.2 (K.comap e.symm.toMonoidHom e.symm.continuous)

/-- Admissibility is unchanged under actual topological group equivalence. -/
theorem isAdmissible_comp_continuousMulEquiv_iff
    (ρ : Representation R G V) (e : H ≃ₜ* G) :
    IsAdmissible (ρ.comp e.toMonoidHom) ↔ IsAdmissible ρ := by
  constructor
  · intro h
    have h' := isAdmissible_comp_continuousMulEquiv (ρ.comp e.toMonoidHom) e.symm h
    have heq : (ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ρ := by
      ext g v
      change ρ (e (e.symm g)) v = ρ g v
      rw [e.apply_symm_apply]
    rwa [heq] at h'
  · exact isAdmissible_comp_continuousMulEquiv ρ e

end Topology
end Langlands
