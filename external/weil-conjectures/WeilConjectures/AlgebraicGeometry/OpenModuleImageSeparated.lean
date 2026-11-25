/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # OpenModuleImageSeparated

Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-uniqueness).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Uniqueness half of the sheaf gluing universal property.
Source: Stacks Project, Cohomology, Tags 08BV and 01EB.
(blueprint: lem-pc-open-module-image-gluing-uniqueness)
Proof: For every test open T and section z of Z(T), the two hypotheses say
l(z) and l'(z) have equal restrictions to T ∩ U and T ∩ V. To see this, write
the transported unit as the ordinary restriction unit followed by pushforward
of the inverse overFunctorEquiv comparison, cancel that isomorphism, and use
restrictAdjunction_unit_app_app. The two opens cover T, so separatedness of the
underlying sheaf gives l(z) = l'(z). Extensionality of linear maps at each T,
then extensionality of module presheaf morphisms, proves l = l'. This proof
also works when X or a cover member is empty or the two members coincide.
-/
theorem schemeOpenModuleImage_pullback_unique
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    {Z : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    {l l' : Z ⟶ M}
    (hu : l ≫ (schemeOpenModuleAdjunction X U).unit.app M =
      l' ≫ (schemeOpenModuleAdjunction X U).unit.app M)
    (hv : l ≫ (schemeOpenModuleAdjunction X V).unit.app M =
      l' ≫ (schemeOpenModuleAdjunction X V).unit.app M) :
    l = l' := by
  have unit_eq (A : X.Opens)
      (h : l ≫ (schemeOpenModuleAdjunction X A).unit.app M =
        l' ≫ (schemeOpenModuleAdjunction X A).unit.app M) :
      l ≫ (Scheme.Modules.restrictAdjunction A.ι).unit.app M =
        l' ≫ (Scheme.Modules.restrictAdjunction A.ι).unit.app M := by
    simp only [schemeOpenModuleAdjunction, Adjunction.ofNatIsoLeft_unit,
      NatTrans.comp_app, Functor.whiskerRight_app, ← Category.assoc] at h
    exact (cancel_mono ((Scheme.Modules.pushforward A.ι).map
      ((Scheme.Modules.overFunctorEquiv A).inv.app M))).mp h
  apply Scheme.Modules.hom_ext
  intro T
  ext z
  apply TopCat.Sheaf.eq_of_locally_eq₂
    (F := ⟨Scheme.Modules.presheaf M, Scheme.Modules.isSheaf M⟩)
    (homOfLE (U.ι.image_preimage_le T))
    (homOfLE (V.ι.image_preimage_le T))
    (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Opens.opensRange_ι, ← inf_sup_right, hcover, top_inf_eq])
  · have h := congrArg (fun k ↦ (Scheme.Modules.Hom.app k T) z) (unit_eq U hu)
    simp only [Scheme.Modules.Hom.comp_app (X := X),
      Scheme.Modules.restrictAdjunction_unit_app_app U.ι, ConcreteCategory.comp_apply] at h
    exact h
  · have h := congrArg (fun k ↦ (Scheme.Modules.Hom.app k T) z) (unit_eq V hv)
    simp only [Scheme.Modules.Hom.comp_app (X := X),
      Scheme.Modules.restrictAdjunction_unit_app_app V.ι, ConcreteCategory.comp_apply] at h
    exact h

end AlgebraicGeometry
