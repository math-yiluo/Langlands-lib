/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

/-- The componentwise restriction-stalk maps are natural in the module sheaf.
Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3).
(blueprint: new-module-restriction-stalk-naturality).

Proof: on a germ represented by a section over an open neighborhood, both
composites apply the module morphism to that section and then pass to its ambient
germ.  Stalk extensionality reduces equality of maps to this germ calculation.
-/
theorem moduleRestrictionStalk_components_natural (X : RingedSpace.{u}) (W : Opens X)
    (x : X) (hx : x ∈ W)
    (c : ∀ F : SheafOfModules.{u} (moduleRings X),
      (ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom).obj
        ((RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩).obj
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F))) ⟶
        (RingedSpace.moduleStalkFunctor X x).obj F)
    (hc : ∀ (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W)
        (hV : (⟨x, hx⟩ : W) ∈ V)
        (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))),
        (c F) (TopCat.Presheaf.germ (C := Ab.{u})
          (X := (X.restrict W.isOpenEmbedding).carrier)
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf
          V ⟨x, hx⟩ hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩ s) :
    ∀ {F G : SheafOfModules.{u} (moduleRings X)} (f : F ⟶ G),
      (ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom).map
        ((RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩).map
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.map
            ((SheafOfModules.overFunctor (moduleRings X) W).map f))) ≫
        c G =
      (c F) ≫ (RingedSpace.moduleStalkFunctor X x).map f := by
  intro F G f
  ext m
  obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (C := Ab.{u}) (X := (X.restrict W.isOpenEmbedding).carrier)
    ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
      ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf m
  change (c G) (RingedSpace.stalkAddMap _ _ _ _) =
    RingedSpace.stalkAddMap _ _ f ((c F) _)
  dsimp only [RingedSpace.stalkAddMap]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [hc, hc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rfl

end AlgebraicGeometry
end
