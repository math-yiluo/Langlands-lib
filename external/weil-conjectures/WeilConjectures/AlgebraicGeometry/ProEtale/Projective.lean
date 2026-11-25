/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-!
# Projectivity of representables on the pro-étale site

## References

* Stacks Project, Tags 00WN and 098F
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- If `D` is w-contractible and `Spec D → X` is weakly étale, the represented sheaf
is projective and sections over it preserve epimorphisms.
-/
theorem proetale_wContractible_projective
    (X : Scheme.{u}) (D : Type u) [CommRing D] [IsWContractibleRing D]
    (f : Spec (.of D) ⟶ X) [WeaklyEtale f] :
    (∀ (F : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ ((ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f))) [Epi φ],
      ∃ s : ((ProEt.topology X).uliftYoneda.{u + 1}.obj (ProEt.mk f)) ⟶ F,
        s ≫ φ = 𝟙 _) ∧
      (∀ (F G : Sheaf (ProEt.topology X) (Type (u + 1)))
        (φ : F ⟶ G) [Epi φ],
        Function.Surjective
          (((sheafToPresheaf (ProEt.topology X) (Type (u + 1))).map φ).app
            (op (ProEt.mk f)))) := by
  have hU : (ProEt.topology X).IsWeaklyContractible.{u + 1} (ProEt.mk f) :=
    ProEt.isWeaklyContractible_of_iso (R := CommRingCat.of D) (Iso.refl _)
  have hsurj (F G : Sheaf (ProEt.topology X) (Type (u + 1)))
      (φ : F ⟶ G) [Epi φ] : Function.Surjective (φ.hom.app (op (ProEt.mk f))) :=
    hU φ ((Sheaf.isLocallySurjective_iff_epi φ).mpr inferInstance)
  refine ⟨?_, hsurj⟩
  intro F φ _
  obtain ⟨x, hx⟩ := hsurj F _ φ ⟨𝟙 (ProEt.mk f)⟩
  refine ⟨(ProEt.topology X).uliftYonedaEquiv.symm x, ?_⟩
  apply (ProEt.topology X).uliftYonedaEquiv.injective
  rw [GrothendieckTopology.uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  exact hx

end AlgebraicGeometry.Scheme
