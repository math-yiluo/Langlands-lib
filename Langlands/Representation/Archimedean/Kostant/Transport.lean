import Langlands.Representation.Archimedean.RealGenericLargeReduction
import Langlands.Algebra.LieEnvelopingEquiv

/-!
# Transport of infinitesimal characters and maximal faithfulness along Lie equivalences

Let `e : L ≃ L'` be an equivalence of complex Lie algebras and `π` a representation of `L`. Put
`π' = π ∘ e⁻¹`, and let `Φ : U(L) ≃ U(L')` be the induced equivalence of enveloping algebras.
Then `π'(Φ u) = π(u)`; `Φ` maps the center onto the center. Hence `π'` has an infinitesimal
character if `π` has one, and `π` is maximally faithful if `π'` is.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.LieEnvelopingEquiv

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L] [LieRing L'] [LieAlgebra ℂ L']
  {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem envelopingAction_comp_enveloping (e : L ≃ₗ⁅ℂ⁆ L') (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (u : UniversalEnvelopingAlgebra ℂ L) :
    envelopingAction (π.comp e.symm.toLieHom) (enveloping e u) = envelopingAction π u := by
  have h : (envelopingAction (π.comp e.symm.toLieHom)).comp (enveloping e).toAlgHom =
      envelopingAction π := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun x => ?_
    change envelopingAction (π.comp e.symm.toLieHom) (enveloping e (UniversalEnvelopingAlgebra.ι ℂ x)) =
      envelopingAction π (UniversalEnvelopingAlgebra.ι ℂ x)
    rw [enveloping_generator]
    simp only [envelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply]
    congr 1
    exact e.symm_apply_apply x
  exact congrArg (fun f : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] Module.End ℂ V => f u) h

theorem mem_center_enveloping_symm (e : L ≃ₗ⁅ℂ⁆ L') {z : UniversalEnvelopingAlgebra ℂ L'}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L')) :
    (enveloping e).symm z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro g
  apply (enveloping e).injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, hz]

theorem mem_center_enveloping (e : L ≃ₗ⁅ℂ⁆ L') {z : UniversalEnvelopingAlgebra ℂ L}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L)) :
    enveloping e z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L') := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro g
  apply (enveloping e).symm.injective
  rw [map_mul, map_mul, AlgEquiv.symm_apply_apply, hz]

theorem hasInfinitesimalCharacter_comp (e : L ≃ₗ⁅ℂ⁆ L') {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hπ : HasInfinitesimalCharacter π) :
    HasInfinitesimalCharacter (π.comp e.symm.toLieHom) := by
  intro z hz
  obtain ⟨c, hc⟩ := hπ _ (mem_center_enveloping_symm e hz)
  refine ⟨c, ?_⟩
  rw [← AlgEquiv.apply_symm_apply (enveloping e) z, envelopingAction_comp_enveloping, hc]

theorem isMaximallyFaithful_of_comp (e : L ≃ₗ⁅ℂ⁆ L') {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hπ : IsMaximallyFaithful (π.comp e.symm.toLieHom)) : IsMaximallyFaithful π := by
  have key : ∀ v ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L') ∧
      envelopingAction (π.comp e.symm.toLieHom) z = 0},
      (enveloping e).symm v ∈ Ideal.span {z | z ∈ Subalgebra.center ℂ
        (UniversalEnvelopingAlgebra ℂ L) ∧ envelopingAction π z = 0} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      refine Ideal.subset_span ⟨mem_center_enveloping_symm e hz.1, ?_⟩
      rw [← envelopingAction_comp_enveloping e π, AlgEquiv.apply_symm_apply, hz.2]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul r x _ hx => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx
  intro u hu
  have h := hπ (enveloping e u) (by rw [envelopingAction_comp_enveloping, hu])
  simpa using key _ h

theorem hasInfinitesimalCharacter_of_comp (e : L ≃ₗ⁅ℂ⁆ L') {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hπ : HasInfinitesimalCharacter (π.comp e.symm.toLieHom)) : HasInfinitesimalCharacter π := by
  intro z hz
  obtain ⟨c, hc⟩ := hπ _ (mem_center_enveloping e hz)
  exact ⟨c, by rw [← hc, envelopingAction_comp_enveloping]⟩

theorem isMaximallyFaithful_comp (e : L ≃ₗ⁅ℂ⁆ L') {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (hπ : IsMaximallyFaithful π) : IsMaximallyFaithful (π.comp e.symm.toLieHom) := by
  refine isMaximallyFaithful_of_comp e.symm ?_
  have h : (π.comp e.symm.toLieHom).comp e.symm.symm.toLieHom = π := by
    ext x
    simp
  rwa [h]

end Langlands.Archimedean.Kostant
