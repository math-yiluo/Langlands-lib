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
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents

/-! # Open restriction does not change a module stalk

Source: Stacks Project, Sheaves, Lemma 00A0, part (3), and Modules, Tag 01CP.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

-- Compare maps on the underlying abelian stalks before introducing scalar transport.
private theorem bijective_of_restrict_germ
    (S : PresheafedSpace AddCommGrpCat.{u}) (U : Opens S) (x : S) (hx : x ∈ U)
    (N : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of U))
    (d : N ≅ (S.restrict U.isOpenEmbedding).presheaf)
    (c : N.stalk ⟨x, hx⟩ → S.presheaf.stalk x)
    (hc : ∀ (V : Opens U) (hV : (⟨x, hx⟩ : U) ∈ V) (s : N.obj (Opposite.op V)),
      c (N.germ V ⟨x, hx⟩ hV s) =
        S.presheaf.germ (U.isOpenEmbedding.isOpenMap.functor.obj V) x
          ⟨⟨x, hx⟩, hV, rfl⟩ (d.hom.app (Opposite.op V) s)) :
    Function.Bijective c := by
  let e := (TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} ⟨x, hx⟩).mapIso d ≪≫
    S.restrictStalkIso U.isOpenEmbedding ⟨x, hx⟩
  have he (m : N.stalk ⟨x, hx⟩) : c m = e.hom m := by
    obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq N m
    change c (N.germ V ⟨x, hx⟩ hV s) =
      (S.restrictStalkIso U.isOpenEmbedding ⟨x, hx⟩).hom
        ((TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} ⟨x, hx⟩).map d.hom
          (N.germ V ⟨x, hx⟩ hV s))
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact (hc V hV s).trans
      (S.restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding V ⟨x, hx⟩ hV
        (d.hom.app (Opposite.op V) s)).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  have h : c = fun m ↦ e.hom m := funext he
  rw [h]
  exact hb

-- Identifying the slice-site restriction with the subspace presheaf unfolds colimit instances.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to an open neighborhood preserves a module stalk after scalar transport.

Source: Stacks Project, Sheaves, Lemma 00A0, part (3); Modules, Tag 01CP,
third paragraph, localization before taking the source-stalk exact sequence.
(blueprint: lem-weil-pbc-module-restriction-stalk-iso)

Proof: Let Y be the restriction of X to U and y the point (x,hxU). The
neighborhood functor from Y to X is final after taking opposites: intersecting
any neighborhood of x with U provides a refinement. Apply the final-functor
colimit comparison to the underlying abelian presheaf of F. This gives an
additive isomorphism from the restricted stalk to F_x, sending the germ of a
section on V in U to the germ of that section on the image of V in X.
The component maps of exists_moduleRestrictionStalk_components satisfy this
same germ formula and are linear over O_{X,x} after restricting scalars along
the inverse restriction-stalk ring map. Since germs jointly generate the
colimit, their underlying additive maps equal the additive comparison above.
They are therefore bijective. Mathlib's isIso_iff_bijective for modules
makes the linear component an isomorphism.
This argument applies to every F, requires no finiteness, and includes the
zero module and zero stalk ring. If U is empty there is no hxU. -/
theorem nonempty_moduleRestrictionStalk_iso
    (X : RingedSpace.{u}) (F : Modules X) (U : Opens X) (x : X) (hxU : x ∈ U) :
    Nonempty
      ((ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv.hom).obj
        ((moduleStalkFunctor (X.restrict U.isOpenEmbedding) ⟨x, hxU⟩).obj
          ((U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U))) ≅
        (moduleStalkFunctor X x).obj F) := by
  classical
  obtain ⟨c, hc⟩ := exists_moduleRestrictionStalk_components X U x hxU
  let S : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, F.val.presheaf⟩
  let N := (U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U)
  -- Identify the presheaves before taking stalks, avoiding a large colimit type comparison.
  let d : N.val.presheaf ≅ (S.restrict U.isOpenEmbedding).presheaf := by
    dsimp only [N, S, TopologicalSpace.Opens.sheafOfModulesEquivOver,
      SheafOfModules.pushforwardPushforwardEquivalence, SheafOfModules.pushforward,
      SheafOfModules.overFunctor, PresheafOfModules.pushforward,
      PresheafOfModules.pushforward₀, PresheafOfModules.pushforward₀Obj,
      PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj,
      PresheafOfModules.presheaf]
    exact Iso.refl _
  have hb : Function.Bijective (c F) :=
    bijective_of_restrict_germ S U x hxU N.val.presheaf d (c F) (hc F)
  have : IsIso (c F) := (ConcreteCategory.isIso_iff_bijective (c F)).mpr hb
  exact ⟨asIso (c F)⟩

end AlgebraicGeometry.RingedSpace
