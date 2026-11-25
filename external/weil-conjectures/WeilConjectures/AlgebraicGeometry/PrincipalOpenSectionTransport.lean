/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Topology.RingedSpaceModuleCohomology

/-! # Canonical section transport to an open subscheme

Source: Stacks Project, Tag 01FM; Mathlib's restriction equivalence.
(blueprint: lem-sc-principal-open-cech-section-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- The canonical additive section identification for restriction to an open subscheme.
Source: Mathlib's `overFunctorEquiv` and `restrictAppIso`; Stacks Project, Tag 01FM.
The map transports the open equality, then applies the inverse of the restriction
comparison. All data are explicit. 
(blueprint: lem-sc-principal-open-cech-section-transport)
-/
noncomputable def principalOpenSectionTransport (A : Type u) [CommRing A]
    (V : (Spec (.of A)).Opens) (M : (Spec (.of A)).Modules) :
    AddCommGrpCat.of ((modulesSpecToSheaf.obj M).obj.obj (op V)) ≅
      (forget₂
        (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat).obj ((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).obj
          ((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
            (Scheme.Modules.overEquiv V).functor).obj M)) :=
  M.presheaf.mapIso (eqToIso V.ι_image_top).op ≪≫
    (M.restrictAppIso V.ι ⊤).symm ≪≫
    ((Scheme.Modules.toPresheaf V.toScheme ⋙
      (evaluation _ _).obj (op ⊤)).mapIso
        ((Scheme.Modules.overFunctorEquiv V).app M).symm)

/-- Canonical section transport is natural in the coefficient module.
Source: Stacks Project, Tag 01FM; naturality of Mathlib's restriction equivalence.
(blueprint: lem-sc-principal-open-cech-section-transport).
Proof: Naturality of the coefficient presheaf transports the open equality. Naturality
of the inverse of overFunctorEquiv then identifies the two composites. -/
theorem principalOpenSectionTransport_natural (A : Type u) [CommRing A]
    (V : (Spec (.of A)).Opens) {M N : (Spec (.of A)).Modules} (g : M ⟶ N)
    (s : (modulesSpecToSheaf.obj M).obj.obj (op V)) :
    (principalOpenSectionTransport A V N).hom ((modulesSpecToSheaf.map g).hom.app (op V) s) =
      ((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        (Scheme.Modules.overEquiv V).functor).map g).app ⊤
          ((principalOpenSectionTransport A V M).hom s) := by
  let e := (Scheme.Modules.overFunctorEquiv V).inv
  have hq := congrArg (fun z ↦ z s)
    (g.mapPresheaf.naturality (eqToHom V.ι_image_top).op)
  have he := congrArg (fun z ↦ (z.app ⊤)
    (M.presheaf.map (eqToHom V.ι_image_top).op s)) (e.naturality g)
  change (e.app N).app ⊤
    (N.presheaf.map (eqToHom V.ι_image_top).op ((g.app V) s)) = _
  change (g.app (V.ι ''ᵁ ⊤)) (M.presheaf.map (eqToHom V.ι_image_top).op s) =
    N.presheaf.map (eqToHom V.ι_image_top).op ((g.app V) s) at hq
  exact (congrArg ((e.app N).app ⊤) hq.symm).trans he

end AlgebraicGeometry
