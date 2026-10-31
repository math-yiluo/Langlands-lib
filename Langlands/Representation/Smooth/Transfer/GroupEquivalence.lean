import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Dual.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! Pullback of algebraic duals and smooth vectors through group equivalences. -/

namespace Langlands

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [TopologicalSpace H] in
/-- The actual algebraic dual commutes with pullback. -/
theorem dual_comp_monoidHom (ρ : Representation ℂ G V) (f : H →* G) :
    Representation.dual (ρ.comp f) = ρ.dual.comp f := by
  ext h ℓ v
  change ℓ (ρ (f h⁻¹) v) = ℓ (ρ (f h)⁻¹ v)
  rw [map_inv]

/-- Smooth vectors are unchanged by pullback through a topological group equivalence. -/
theorem isSmoothVector_comp_continuousMulEquiv_iff
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G) (v : V) :
    IsSmoothVector (ρ.comp e.toMonoidHom) v ↔ IsSmoothVector ρ v := by
  constructor
  · intro hv
    have h := isSmoothVector_comp e.symm.toMonoidHom e.symm.continuous hv
    have heq : (ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ρ := by
      ext g x
      change ρ (e (e.symm g)) x = ρ g x
      rw [e.apply_symm_apply]
    rwa [heq] at h
  · exact isSmoothVector_comp e.toMonoidHom e.continuous

/-- Smooth dual vectors are transported through the actual dual action. -/
theorem isSmoothVector_dual_comp_continuousMulEquiv_iff
    (ρ : Representation ℂ G V) (e : H ≃ₜ* G) (ℓ : Module.Dual ℂ V) :
    IsSmoothVector (Representation.dual (ρ.comp e.toMonoidHom)) ℓ ↔ IsSmoothVector ρ.dual ℓ := by
  rw [dual_comp_monoidHom]
  exact isSmoothVector_comp_continuousMulEquiv_iff ρ.dual e ℓ

end Langlands
