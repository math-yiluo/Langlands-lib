/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData

/-! # Coherence of the specified tensor-pullback comparisons

## Implementation details

Conjugate the ordinary pullback unit equations by the specified tensor-to-ordinary
isomorphisms, cancel inverse pairs and use naturality. Equality transport commutes with the
comparison family. Combine the two unit equations by cancellation against the composition
isomorphism. Naturality of the identity comparison applied to the quotient gives its square.

## References

* Stacks Project, Sheaves, Tag 0097
* Constructions Tag 01O3
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Associativity transported from the ordinary module-pullback pseudofunctor. -/
theorem projectiveBundlePullback_associativity
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (projectiveBundlePullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (projectiveBundlePullbackComp g h).inv _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (projectiveBundlePullbackComp f g).hom ≫
        (projectiveBundlePullbackComp (f ≫ g) h).hom = eqToHom (by simp) := by
  unfold projectiveBundlePullbackComp
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  apply NatTrans.ext
  funext F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have hn := congrArg (fun t ↦ (Scheme.Modules.tensorPullback f).map t)
    ((projectiveBundleTensorPullbackIso g).hom.naturality
      ((projectiveBundleTensorPullbackIso h).inv.app F))
  simp only [Functor.map_comp] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (projectiveBundleTensorPullbackIso f).inv.naturality_assoc]
  rw [(projectiveBundleTensorPullbackIso f).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [(projectiveBundleTensorPullbackIso (f ≫ g)).hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  have hs := (Scheme.Modules.pullbackComp f g).hom.naturality
    ((projectiveBundleTensorPullbackIso h).inv.app F)
  simp only [Functor.comp_map] at hs
  rw [reassoc_of% hs]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  have ha := congrArg (fun k ↦ k.app F)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp] at ha
  rw [reassoc_of% ha]
  have he := congrArg (fun k ↦ k.app F) (eqToHom_iso_hom_naturality
    (fun g : W ⟶ Z ↦ projectiveBundleTensorPullbackIso g) (Category.assoc f g h).symm)
  simp only [NatTrans.comp_app] at he
  rw [reassoc_of% he, Iso.hom_inv_id_app]
  simp

end AlgebraicGeometry
