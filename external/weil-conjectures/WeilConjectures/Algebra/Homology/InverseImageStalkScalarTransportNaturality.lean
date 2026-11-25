/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Topology.InverseImageModule
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Natural semilinear inverse-image stalk comparison

Source: Stacks Project, Sheaves, Tags 008H and 0098.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def explicitStalkMap
    (C : Type (u + 1)) [Category.{u} C] [Limits.HasColimits.{u} C]
    {T Z : TopCat.{u}} (f : T ⟶ Z) (x : T)
    [HasWeakSheafify (Opens.grothendieckTopology T) C] (G : Z.Sheaf C) :
    TopCat.Presheaf.stalk G.obj (f x) ⟶
      TopCat.Presheaf.stalk ((TopCat.Sheaf.inverseImageConstruction f C).obj G).obj x :=
  TopCat.Presheaf.stalkPullbackHom C f G.obj x ≫
    (TopCat.Presheaf.stalkFunctor C x).map
      (toSheafify (Opens.grothendieckTopology T)
        ((TopCat.Presheaf.pullback C f).obj G.obj))

private theorem explicitStalkMap_germ
    (C : Type (u + 1)) [Category.{u} C] [Limits.HasColimits.{u} C]
    {T Z : TopCat.{u}} (f : T ⟶ Z) (x : T)
    [HasWeakSheafify (Opens.grothendieckTopology T) C] (G : Z.Sheaf C)
    (V : Opens Z) (hx : f x ∈ V) :
    TopCat.Presheaf.germ G.obj V (f x) hx ≫ explicitStalkMap C f x G =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) C (Opens.grothendieckTopology Z)
          (Opens.grothendieckTopology T)).unit.app G).hom.app (Opposite.op V) ≫
        TopCat.Presheaf.germ
          ((TopCat.Sheaf.inverseImageConstruction f C).obj G).obj
          ((Opens.map f).obj V) x hx := by
  dsimp only [explicitStalkMap]
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc]
  congr 1
  change _ = ((sheafToPresheaf (Opens.grothendieckTopology Z) C).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) C (Opens.grothendieckTopology Z)
        (Opens.grothendieckTopology T)).unit.app G)).app (Opposite.op V)
  dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Adjunction.comp_unit_app, TopCat.Presheaf.pullbackPushforwardAdjunction,
    TopCat.Presheaf.pullback]

-- Naturality is categorical; prove it before exposing the concrete stalk module structures.
private theorem explicitStalkMap_naturality
    (C : Type (u + 1)) [Category.{u} C] [Limits.HasColimits.{u} C]
    {T Z : TopCat.{u}} (f : T ⟶ Z) (x : T)
    [HasWeakSheafify (Opens.grothendieckTopology T) C]
    {G H : Z.Sheaf C} (a : G ⟶ H) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map a.hom ≫ explicitStalkMap C f x H =
      explicitStalkMap C f x G ≫ (TopCat.Presheaf.stalkFunctor C x).map
        (((TopCat.Sheaf.inverseImageConstruction f C).map a).hom) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hx
  simp only [← Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ, explicitStalkMap_germ]
  simp only [Category.assoc]
  rw [explicitStalkMap_germ, TopCat.Presheaf.stalkFunctor_map_germ]
  simp only [← Category.assoc]
  congr 1
  exact congrArg (fun q ↦ q.hom.app (Opposite.op V))
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) C (Opens.grothendieckTopology Z)
        (Opens.grothendieckTopology T)).unit_naturality a).symm

set_option backward.defeqAttrib.useBackward true in
/-- Natural semilinear comparison for the explicitly constructed inverse image.
Source: Stacks Project, Sheaves, Tag 0098, proof using Tag 008H.

Proof: use the explicit sheaf pullback construction, namely presheaf pullback
followed by sheafification. Apply the ring and abelian stalk comparisons of Tag
008H directly to this construction.
The ring map is stalkPullbackHom followed by stalk of toSheafify; both are
isomorphisms. The analogous abelian map defines c. To verify
semilinearity, represent the scalar and vector on neighborhoods of f(x), restrict
both to their intersection, and apply the germ formulas for the two comparisons.
The semilinearity clause of exists_inverseImageModuleInstances identifies the
unit of r times m with the product of the two units. The stalk germ scalar law
then gives the asserted equation. For naturality, represent m by a germ, use
naturality of the abelian inverse-image unit, and use stalkFunctor_map_germ_apply.
The map on the right is exactly stalkAddMap of inverseImageModuleMap by definition.
The construction applies to zero modules and zero rings; with empty X there is
no x. No flatness or nonvanishing hypothesis is used.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality). -/
theorem exists_inverseImage_stalk_comparison_natural
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier) (x : X) :
    let k : Y.presheaf.stalk (f x) ⟶
        TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
          (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x :=
      TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    ∃ (c : ∀ M : RingedSpace.Modules Y,
      (RingedSpace.moduleStalkFunctor Y (f x)).obj M ≃+
        TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
          (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x),
      (∀ (M : RingedSpace.Modules Y) (r : Y.presheaf.stalk (f x))
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        c M (r • m) = k.hom r • c M m) ∧
      ∀ (M N : RingedSpace.Modules Y) (a : M ⟶ N)
      (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
      c N ((RingedSpace.moduleStalkFunctor Y (f x)).map a m) =
      PresheafOfModules.stalkAddMap
          (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a).val (c M m) := by
  classical
  dsimp only
  let kA (M : RingedSpace.Modules Y) :=
    explicitStalkMap Ab f x ((SheafOfModules.toSheaf _).obj M)
  have hkA (M : RingedSpace.Modules Y) : IsIso (kA M) := by
    have : IsIso (TopCat.Presheaf.stalkPullbackHom Ab f M.val.presheaf x) :=
      (TopCat.Presheaf.stalkPullbackIso Ab f M.val.presheaf x).isIso_hom
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab
      ((TopCat.Presheaf.pullback Ab f).obj M.val.presheaf)
    change IsIso (TopCat.Presheaf.stalkPullbackHom Ab f M.val.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor Ab x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback Ab f).obj M.val.presheaf)))
    infer_instance
  let c (M : RingedSpace.Modules Y) := (asIso (kA M)).addCommGroupIsoToAddEquiv
  have hc (M : RingedSpace.Modules Y) (V : Opens Y) (hx : f x ∈ V)
      (m : M.val.obj (Opposite.op V)) :
      c M (TopCat.Presheaf.germ M.val.presheaf V (f x) hx m) =
        TopCat.Presheaf.germ (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf
          ((Opens.map f).obj V) x hx
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map f) Ab (Opens.grothendieckTopology Y)
              (Opens.grothendieckTopology X)).unit.app
                ((SheafOfModules.toSheaf _).obj M)).hom.app (Opposite.op V) m) := by
    exact ConcreteCategory.congr_hom
      (explicitStalkMap_germ Ab f x ((SheafOfModules.toSheaf _).obj M) V hx) m
  refine ⟨c, ?_, ?_⟩
  · intro M r m
    obtain ⟨U, hxU, r, rfl⟩ := Y.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    have hx : f x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← Y.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) (f x) hx r,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) (f x) hx m,
      ← PresheafOfModules.germ_smul (R := Y.presheaf) M.val]
    erw [hc M (U ⊓ V) hx]
    have hu := (Classical.choose_spec
      (TopCat.Sheaf.exists_inverseImageModuleInstances f Y.sheaf M)).2
    have hs := hu (Opposite.op (U ⊓ V))
      (Y.presheaf.map (homOfLE inf_le_left).op r)
      (M.val.map (homOfLE inf_le_right).op m)
    erw [hs]
    erw [PresheafOfModules.germ_smul
      (R := (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj)
      (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val]
    erw [hc M (U ⊓ V) hx]
    have hr := ConcreteCategory.congr_hom
      (explicitStalkMap_germ CommRingCat f x Y.sheaf (U ⊓ V) hx)
      (Y.presheaf.map (homOfLE inf_le_left).op r)
    exact congrArg (fun r ↦ r • _) hr.symm
  · intro M N a m
    exact ConcreteCategory.congr_hom
      (explicitStalkMap_naturality Ab f x ((SheafOfModules.toSheaf _).map a)) m

end
