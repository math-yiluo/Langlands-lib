import Langlands.Representation.Smooth.FixedVectors.GroupEquivalenceGenerationStatement

/-! # Proof of fixed-vector generation under a group equivalence -/

set_option autoImplicit false

namespace Langlands

universe uR uG uH uV

variable {R : Type uR} [CommRing R]
  {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- The fixed-vector generation property survives a change of group
through an actual group equivalence. -/
theorem fixedVectors_generate_comp_mulEquiv_iff
    (ρ : Representation R G V) (e : H ≃* G) (K : Subgroup H) :
    (∀ S : Subrepresentation (ρ.comp e.toMonoidHom),
      fixedVectors (ρ.comp e.toMonoidHom) K ≤ S.toSubmodule → S = ⊤) ↔
    (∀ S : Subrepresentation ρ,
      fixedVectors ρ (K.comap e.symm.toMonoidHom) ≤ S.toSubmodule → S = ⊤) := by
  constructor
  · intro hgen S hS
    let C : Subrepresentation (ρ.comp e.toMonoidHom) :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := fun h _ hv => S.apply_mem_toSubmodule (e h) hv }
    have hC : C = ⊤ := hgen C (by
      change fixedVectors (ρ.comp e.toMonoidHom) K ≤ S.toSubmodule
      rw [fixedVectors_comp_mulEquiv ρ e K]
      exact hS)
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    exact congrArg
      (fun T : Subrepresentation (ρ.comp e.toMonoidHom) => T.toSubmodule) hC
  · intro hgen S hS
    let C : Subrepresentation ρ :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := by
          intro g v hv
          have h := S.apply_mem_toSubmodule (e.symm g) hv
          change ρ (e (e.symm g)) v ∈ S.toSubmodule at h
          simpa only [MulEquiv.apply_symm_apply] using h }
    have hC : C = ⊤ := hgen C (by
      change fixedVectors ρ (K.comap e.symm.toMonoidHom) ≤ S.toSubmodule
      rw [← fixedVectors_comp_mulEquiv ρ e K]
      exact hS)
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    exact congrArg (fun T : Subrepresentation ρ => T.toSubmodule) hC

/-- Group equivalences preserve generation by the corresponding fixed vectors. -/
theorem fixedVectorsGroupEquivalenceGeneration :
    FixedVectorsGroupEquivalenceGenerationStatement.{uR, uG, uH, uV} := by
  intro R _ G _ H _ V _ _ ρ e K
  exact fixedVectors_generate_comp_mulEquiv_iff ρ e K

end Langlands
