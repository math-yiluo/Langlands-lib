/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Stalk functor for modules on a ringed space

Source: Stacks Project, Cohomology, Lemma 06YB, label `lemma-check-K-flat-stalks`
(blueprint: def-pc-module-stalk-functor).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TopCat.Presheaf

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u}) (x : X)

/-- (blueprint: def-pc-module-stalk-functor) The category of sheaves of modules over the structure
sheaf of the ringed space `X`; Stacks, Cohomology, Lemma 06YB. -/
abbrev Modules := SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)

/-- (blueprint: def-pc-module-stalk-functor) The additive map on stalks at `x` induced by a
morphism of sheaves of modules; Stacks, Cohomology, Lemma 06YB. -/
def stalkAddMap {M N : Modules X} (f : M ⟶ N) :
    TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.val.presheaf x →+
      TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) N.val.presheaf x :=
  ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map f.val))

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: def-pc-module-stalk-functor) A morphism of sheaves of modules over a
ringed space induces a linear map on stalks at `x`. Stacks, Cohomology, Lemma 06YB.
Linearity follows by representing both a scalar and a vector by germs on a common
open neighborhood and using compatibility of the sheaf morphism with scalar action. -/
theorem stalkMap_linear {M N : Modules X} (f : M ⟶ N) :
    ∀ (r : X.presheaf.stalk x)
      (m : TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.val.presheaf x),
      stalkAddMap X x f (r • m) = r • stalkAddMap X x f m := by
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
    ← PresheafOfModules.germ_smul (R := X.presheaf) M.val]
  dsimp only [stalkAddMap]
  erw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply]
  change TopCat.Presheaf.germ N.val.presheaf _ x hx ((f.val.app _).hom (_ • _)) = _
  rw [map_smul, PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rfl

/-- (blueprint: def-pc-module-stalk-functor) The stalk map of a module-sheaf morphism,
viewed as a morphism of modules over the stalk ring. Stacks, Cohomology, Lemma 06YB. -/
def moduleStalkMap {M N : Modules X} (f : M ⟶ N) :
    ModuleCat.of (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.val.presheaf x) ⟶
    ModuleCat.of (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) N.val.presheaf x) :=
  ModuleCat.ofHom
    { toFun := stalkAddMap X x f
      map_add' := (stalkAddMap X x f).map_add
      map_smul' := stalkMap_linear X x f }

/-- (blueprint: def-pc-module-stalk-functor) The stalk map preserves identities.
Stacks, Cohomology, Lemma 06YB. This follows from the identity law for the
underlying stalk functor on abelian-group presheaves. -/
theorem moduleStalkMap_id (M : Modules X) :
    moduleStalkMap X x (𝟙 M) = 𝟙 _ := by
  ext m
  change (stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map (𝟙 M.val)) m = m
  simp

/-- (blueprint: def-pc-module-stalk-functor) The stalk map preserves composition.
Stacks, Cohomology, Lemma 06YB. This follows from the composition law for the
underlying stalk functor on abelian-group presheaves. -/
theorem moduleStalkMap_comp {M N P : Modules X} (f : M ⟶ N) (g : N ⟶ P) :
    moduleStalkMap X x (f ≫ g) = moduleStalkMap X x f ≫ moduleStalkMap X x g := by
  ext m
  change (stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map (f ≫ g).val) m =
    (stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map g.val)
      ((stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map f.val) m)
  rw [SheafOfModules.comp_val, Functor.map_comp, Functor.map_comp]
  rfl

/-- (blueprint: def-pc-module-stalk-functor) The stalk at `x` of a sheaf of
modules on a ringed space is a module over the stalk ring. Stacks, Cohomology,
Lemma 06YB. Morphisms act by their linear maps on stalks. -/
def moduleStalkFunctor : Modules X ⥤ ModuleCat.{u} (X.presheaf.stalk x) where
  obj M := ModuleCat.of _
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier) M.val.presheaf x)
  map f := moduleStalkMap X x f
  map_id M := moduleStalkMap_id X x M
  map_comp f g := moduleStalkMap_comp X x f g

/-- (blueprint: def-pc-module-stalk-functor) Stalks take zero morphisms of
sheaves of modules to zero morphisms of stalk modules. Stacks, Cohomology,
Lemma 06YB. This follows because stalks are filtered colimits in abelian
groups and the maps on stalks are induced by the sectionwise zero maps. -/
theorem moduleStalkFunctor_preservesZeroMorphisms_proof :
    (moduleStalkFunctor X x).PreservesZeroMorphisms := by
  constructor
  intro M N
  ext m
  change (stalkFunctor Ab x).map ((PresheafOfModules.toPresheaf _).map (0 : M ⟶ N).val) m = 0
  have h : (0 : M ⟶ N).val = 0 := rfl
  rw [h, Functor.map_zero, Functor.map_zero]
  rfl

/-- (blueprint: def-pc-module-stalk-functor) The zero-morphism preservation
instance for the module stalk functor; Stacks, Cohomology, Lemma 06YB. -/
instance moduleStalkFunctor_preservesZeroMorphisms :
    (moduleStalkFunctor X x).PreservesZeroMorphisms :=
  moduleStalkFunctor_preservesZeroMorphisms_proof X x

end AlgebraicGeometry.RingedSpace

end
