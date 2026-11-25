/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitionCoherence

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- For a ringed space X and global module sheaf F, the counit at the top open is an isomorphism.
There are maps iota(W,W') from the sheafified extension of F restricted to W to the sheafified
extension of F restricted to W', for W contained in W'. Their adjunction transposes are the
restrictions of the W' unit transported by overFunctorMap; iota(W,W) is identity, composites are
iota(W,W''), and iota(W,top) followed by the top counit is the W counit. For x in W there is an
isomorphism from F_x to the W extension stalk whose inverse is the stalk of the W counit; these
isomorphisms intertwine the transition stalk maps.

Proof: Use the inside-open stalk calculation and adjunction triangle identities to see that the
counit for F restricted to W induces an isomorphism at every x in W: the restriction-stalk
comparison identifies its composition with the unit with identity. For W=top this proves the
counit is an isomorphism of sheaves by the stalk criterion. For W <= W', define iota as the
inverse homEquiv image of the displayed transported restriction of the W' unit. This gives the
first equation by inverse cancellation. At W=W', the restriction transport is identity, so
homEquiv sends both iota and identity to the W unit; injectivity proves their equality. For W <=
W' <= W'', restrict the transpose equations to W and use naturality of the units and coherence of
overFunctorMap. Their composite is the restriction of the W'' unit; homEquiv injectivity gives
composition. Applying counits to the same equations and using the triangle identities gives
iota(W,W') followed by the W' counit equals the W counit; specialize W'=top. Finally take e(W,x)
to be the inverse of the counit's stalk isomorphism already obtained. Functoriality on stalks
applied to that counit compatibility says iota_x followed by e(W',x).inv equals e(W,x).inv. Cancel
these isomorphisms to get the final equation. This construction works for independently chosen
adjunctions because only their own units, counits and triangle identities are used. Source: Stacks
Project, Sheaves Lemma 00A7 (2)-(4) and Lemma 00A5.
(blueprint: lem-sc-module-extension-by-zero-stalk-maps-transitions) -/
theorem moduleExtensionByZero_stalk_transitions (X : RingedSpace.{u}) :
    (∀ F : SheafOfModules.{u} (moduleRings X),
      IsIso ((Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F) ∧
      ∃ iota : (∀ (W W' : Opens X), W ≤ W' →
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F) ⟶
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))),
        (∀ (W W' : Opens X) (h : W ≤ W'),
          (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _
              (iota W W' h) =
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
              (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
                ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
              (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))) ∧
        (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
        (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
          iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
        (∀ W : Opens X,
          iota W ⊤ le_top ≫
              (Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F =
            (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app F) ∧
        ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
            ((RingedSpace.moduleStalkFunctor X x).obj F ≅
              (RingedSpace.moduleStalkFunctor X x).obj
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
          (∀ (W : Opens X) (x : X) (hx : x ∈ W),
            (e W x hx).inv =
              (RingedSpace.moduleStalkFunctor X x).map
                ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app
                  F)) ∧
          (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
            (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
              (e W' x (h hx)).hom)) := by
  intro F
  refine ⟨?_, ?_⟩
  · let ff : (SheafOfModules.overFunctor.{u} (moduleRings X) ⊤).FullyFaithful :=
      { preimage := fun g ↦
          { val :=
              { app := fun U ↦ g.val.app (op (Over.mk (homOfLE (le_top : U.unop ≤ ⊤))))
                naturality := by
                  intro U V f
                  exact g.val.naturality
                    (Over.homMk (U := Over.mk (homOfLE (le_top : V.unop ≤ ⊤)))
                      (V := Over.mk (homOfLE (le_top : U.unop ≤ ⊤)))
                      f.unop (by subsingleton)).op } }
        map_preimage := by
          intro M N g
          ext U x
          rfl
        preimage_map := by
          intro M N g
          ext U x
          rfl }
    let := ff.full
    let := ff.faithful
    infer_instance
  · let iota := fun (W W' : Opens X) (h : W ≤ W') ↦
        ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _).symm
          ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
            (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
              ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
                ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)))
    refine ⟨iota, ?_, ModuleExtensionByZeroStalkTransitionCoherence X F⟩
    intro W W' h
    exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry
