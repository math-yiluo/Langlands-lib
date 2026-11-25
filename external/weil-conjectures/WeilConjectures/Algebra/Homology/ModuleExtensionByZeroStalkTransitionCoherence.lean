/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import Mathlib.Geometry.RingedSpace.Stalks

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The transitions explicitly transposed from the restricted units satisfy identity,
composition and counit compatibility, and the inside-open counit stalks give compatible
isomorphisms. Source: Stacks Project, Sheaves, Tag 00A7 (2)-(4) and Tag 00A5.

Proof: Denote extension and restriction at W by L_W and R_W, with unit eta_W and counit eps_W.
The displayed iota is defined by the inverse adjunction hom-equivalence, not by choosing an
existence witness. For W = W', the restriction transport is the identity on every section and
the transported unit is eta_W; the transpose of identity is eta_W, so injectivity of the
hom-equivalence gives the identity equation. Transpose iota(W,W') followed by eps_W':
naturality of the hom-equivalence, naturality of the restriction transport and the right
triangle identities at W and W' reduce it to identity on R_W F, which is the transpose of
eps_W. This proves counit compatibility for every W', including top.

The existing moduleExtensionByZero_unit_isIso theorem makes eta_W invertible. The right
triangle identity then makes R_W eps_W its inverse. For W contained in W', restriction
transport identifies R_W eps_W' with a conjugate of the further restriction of R_W' eps_W',
so it too is invertible. To prove composition for W <= W' <= W'', transpose both candidate
maps at W and cancel R_W eps_W''. Naturality of transposition and the general counit
compatibility equation reduce both sides to the transpose of eps_W.

At x in W, forget R_W eps_W to abelian presheaves on W; its components are invertible.
The usual restriction-stalk comparisons conjugate its stalk map to the underlying abelian
stalk map of eps_W. Check this equality on germs using the restriction-stalk germ formulas
and naturality of stalk maps. Thus the underlying stalk map is invertible, and the forgetful
functor from modules to abelian groups reflects isomorphisms. Define e(W,x) as the inverse
of asIso of the counit stalk map, which determines e uniquely and gives its inverse formula.
Apply the stalk functor to general counit compatibility and cancel e(W',x).inv to obtain
the final equation. All stalk maps are O_X,x-linear. The argument uses the units of the
chosen adjunctions themselves and requires no agreement between separate choices. Empty W
has no inside points; equal opens and the top open require no extra hypotheses.
(blueprint: new-module-extension-by-zero-coherence) -/
theorem ModuleExtensionByZeroStalkTransitionCoherence (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) :
    let iota := fun (W W' : Opens X) (h : W ≤ W') ↦
      ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _).symm
      ((SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
        (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
          ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
            ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
        (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
          ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)))
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
          (e W' x (h hx)).hom) := by
  classical
  intro iota
  let A (W : Opens X) := Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2
  have hi (W : Opens X) : iota W W le_rfl = 𝟙 _ := by
    apply (A W).homEquiv _ _ |>.injective
    change ((A W).homEquiv _ _) (((A W).homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_id]
    ext U s
    rfl
  have hc (W W' : Opens X) (h : W ≤ W') :
      iota W W' h ≫ (A W').counit.app F = (A W).counit.app F := by
    apply (A W).homEquiv _ _ |>.injective
    rw [Adjunction.homEquiv_naturality_right]
    change ((A W).homEquiv _ _) (((A W).homEquiv _ _).symm _) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    rw [(A W).right_triangle_components]
    simp only [Category.assoc]
    rw [← (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    change _ ≫ (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
      ((A W').unit.app _ ≫ (SheafOfModules.overFunctor (moduleRings X) W').map
        ((A W').counit.app F)) ≫ _ = _
    rw [(A W').right_triangle_components]
    simp
  -- The right triangle makes the restricted counit inverse to the invertible unit.
  have hr (W : Opens X) :
      IsIso ((SheafOfModules.overFunctor (moduleRings X) W).map ((A W).counit.app F)) := by
    have : IsIso ((A W).unit.app
        ((SheafOfModules.overFunctor (moduleRings X) W).obj F)) :=
      moduleExtensionByZero_unit_isIso X W _
    have he : (SheafOfModules.overFunctor (moduleRings X) W).map ((A W).counit.app F) =
        inv ((A W).unit.app ((SheafOfModules.overFunctor (moduleRings X) W).obj F)) := by
      apply (cancel_epi ((A W).unit.app _)).mp
      rw [(A W).right_triangle_components, IsIso.hom_inv_id]
      rfl
    rw [he]
    infer_instance
  -- Restrict this inverse further along a nested inclusion.
  have hr' (W W' : Opens X) (h : W ≤ W') :
      IsIso ((SheafOfModules.overFunctor (moduleRings X) W).map ((A W').counit.app F)) := by
    let t := SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)
    have := hr W'
    have he : (SheafOfModules.overFunctor (moduleRings X) W).map ((A W').counit.app F) =
        t.inv.app _ ≫ (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
          ((SheafOfModules.overFunctor (moduleRings X) W').map ((A W').counit.app F)) ≫
          t.hom.app F := by
      simpa only [Functor.comp_map, Functor.id_obj, Iso.inv_hom_id_app_assoc] using
        (congrArg (fun k ↦ t.inv.app _ ≫ k)
          (t.hom.naturality ((A W').counit.app F))).symm
    rw [he]
    infer_instance
  refine ⟨hi, ?_, fun W ↦ hc W ⊤ le_top, ?_⟩
  · intro W W' W'' h h'
    have := hr' W W'' (h.trans h')
    -- Transpose and cancel the restricted later counit; use the general counit equation.
    apply (A W).homEquiv _ _ |>.injective
    apply (cancel_mono ((SheafOfModules.overFunctor (moduleRings X) W).map
      ((A W'').counit.app F))).mp
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
    rw [Category.assoc, hc W' W'' h', hc W W' h, hc W W'' (h.trans h')]
  · have hs (W : Opens X) (x : X) (hx : x ∈ W) :
        IsIso ((RingedSpace.moduleStalkFunctor X x).map ((A W).counit.app F)) := by
      -- Work with abelian presheaves to avoid unnecessary scalar transports.
      let Y := X.restrict (Opens.isOpenEmbedding W)
      let E := (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
        PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
          ((SheafOfModules.overFunctor (moduleRings X) W).obj F)
      let S : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, E.val.presheaf⟩
      let T : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, F.val.presheaf⟩
      let f := Functor.whiskerLeft W.isOpenEmbedding.functor.op
        ((PresheafOfModules.toPresheaf _).map ((A W).counit.app F).val)
      have hf (V : (Opens W)ᵒᵖ) : IsIso (f.app V) := by
        have := hr W
        let U := W.isOpenEmbedding.functor.obj V.unop
        let j : U ⟶ W := homOfLE (Set.image_subset_iff.2 (fun y _ ↦ y.2))
        have : IsIso (((SheafOfModules.forget ((moduleRings X).over W) ⋙
            PresheafOfModules.toPresheaf ((moduleRings X).over W).obj).map
            ((SheafOfModules.overFunctor (moduleRings X) W).map
              ((A W).counit.app F))).app (op (Over.mk j))) := by
          infer_instance
        exact this
      have : IsIso f := NatIso.isIso_of_isIso_app f
      let c := S.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩
      let d := T.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩
      let g := (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map
        ((RingedSpace.moduleStalkFunctor X x).map ((A W).counit.app F))
      have he : (TopCat.Presheaf.stalkFunctor (X := Y.carrier) AddCommGrpCat.{u}
          ⟨x, hx⟩).map f ≫ d.hom = c.hom ≫ g := by
        apply TopCat.Presheaf.stalk_hom_ext (X := Y.carrier) (S.restrict W.isOpenEmbedding).presheaf
        intro V hV
        rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
        erw [T.restrictStalkIso_hom_eq_germ W.isOpenEmbedding V ⟨x, hx⟩ hV]
        rw [← Category.assoc]
        erw [S.restrictStalkIso_hom_eq_germ W.isOpenEmbedding V ⟨x, hx⟩ hV]
        change _ = _ ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map ((A W).counit.app F).val)
        erw [TopCat.Presheaf.stalkFunctor_map_germ]
        rfl
      have : IsIso (c.hom ≫ g) := by rw [← he]; infer_instance
      have : IsIso g := IsIso.of_isIso_comp_left c.hom g
      exact isIso_of_reflects_iso _
        (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})
    let e := fun (W : Opens X) (x : X) (hx : x ∈ W) ↦
      letI := hs W x hx
      (asIso ((RingedSpace.moduleStalkFunctor X x).map ((A W).counit.app F))).symm
    refine ⟨e, fun W x hx ↦ rfl, ?_⟩
    intro W W' h x hx
    apply (cancel_mono (e W' x (h hx)).inv).mp
    change ((e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h)) ≫
      (RingedSpace.moduleStalkFunctor X x).map ((A W').counit.app F) = _
    rw [Category.assoc, ← Functor.map_comp, hc W W' h]
    change (e W x hx).hom ≫ (e W x hx).inv =
      (e W' x (h hx)).hom ≫ (e W' x (h hx)).inv
    simp

end AlgebraicGeometry
