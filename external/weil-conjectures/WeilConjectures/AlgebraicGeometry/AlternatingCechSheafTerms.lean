/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Increasing-tuple sheaf terms as products of open direct images

Source: Stacks Project, Tag 01FM, intersection terms; the over-site restriction adjunction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-terms).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

private noncomputable def capProductIso {X : Scheme.{u}} (W V : X.Opens) :
    W ⨯ V ≅ V ⊓ W where
  hom := homOfLE (le_inf (leOfHom prod.snd) (leOfHom prod.fst))
  inv := prod.lift (homOfLE inf_le_right) (homOfLE inf_le_left)
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

private noncomputable def capIsoOver {X : Scheme.{u}} (G : X.Modules) (W : X.Opens) :
    cechCapModule G W ≅
      ((SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).obj (G.over W)).val := by
  let H := (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).obj (G.over W)
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · refine
      { hom := ModuleCat.ofHom (X := (cechCapModule G W).obj V) (Y := H.val.obj V)
          { toFun := fun s ↦ G.val.map (capProductIso W V.unop).hom.op s
            map_add' := by intros; simp
            map_smul' := ?_ }
        inv := ModuleCat.ofHom (X := H.val.obj V) (Y := (cechCapModule G W).obj V)
          { toFun := fun s ↦ G.val.map (capProductIso W V.unop).inv.op s
            map_add' := by intros; simp
            map_smul' := ?_ }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro a s
      change G.val.map (capProductIso W V.unop).hom.op
          ((X.ringCatSheaf.obj.map
            (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a) •
              (show G.val.obj (op (V.unop ⊓ W)) from s)) =
        (X.ringCatSheaf.obj.map (prod.snd : W ⨯ V.unop ⟶ V.unop).op a) •
          G.val.map (capProductIso W V.unop).hom.op s
      rw [PresheafOfModules.map_smul]
      congr 1
      rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 2
    · intro a s
      change G.val.map (capProductIso W V.unop).inv.op
          ((X.ringCatSheaf.obj.map (prod.snd : W ⨯ V.unop ⟶ V.unop).op a) •
            (show G.val.obj (op (W ⨯ V.unop)) from s)) =
        (X.ringCatSheaf.obj.map
          (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a) •
            G.val.map (capProductIso W V.unop).inv.op s
      rw [PresheafOfModules.map_smul]
      congr 1
      rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 2
    · ext s
      change G.val.map (capProductIso W V.unop).inv.op
          (G.val.map (capProductIso W V.unop).hom.op s) = s
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.inv_hom_id]
      exact ConcreteCategory.congr_hom (G.val.presheaf.map_id _) s
    · ext s
      change G.val.map (capProductIso W V.unop).hom.op
          (G.val.map (capProductIso W V.unop).inv.op s) = s
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.hom_inv_id]
      exact ConcreteCategory.congr_hom (G.val.presheaf.map_id _) s
  · intro V Z h
    ext s
    change G.val.map (capProductIso W Z.unop).hom.op
        (G.val.map (homOfLE (inf_le_inf_right W (leOfHom h.unop))).op s) =
      G.val.map (prod.map (𝟙 W) h.unop).op
        (G.val.map (capProductIso W V.unop).hom.op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
      ← op_comp, ← op_comp]
    congr 2

private noncomputable def capSheafificationIsoPushforward
    {X : Scheme.{u}} (G : X.Modules) (W : X.Opens) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (cechCapModule G W) ≅
      (Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι) := by
  let H := (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).obj (G.over W)
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) W).comp
    (Scheme.Modules.overEquiv W).toAdjunction
  let adj' := adj.ofNatIsoLeft (Scheme.Modules.overFunctorEquiv W)
  let e := Adjunction.rightAdjointUniq adj' (Scheme.Modules.restrictAdjunction W.ι)
  refine L.mapIso (capIsoOver G W) ≪≫ ?_ ≪≫
    (SheafOfModules.pushforward (SheafOfModules.pushforwardOver W)).mapIso
      ((Scheme.Modules.overEquiv W).unitIso.app (G.over W)) ≪≫
    e.app ((Scheme.Modules.overEquiv W).functor.obj (G.over W)) ≪≫
    (Scheme.Modules.pushforward W.ι).mapIso ((Scheme.Modules.overFunctorEquiv W).app G)
  exact (asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit).app H

/-- Each increasing-tuple term is a product of direct images from its intersections.
Source: Stacks Project, Tag 01FM, ordered intersection terms, and the construction
paragraph of lem-pc-s3-affine-alternating-cech-augmented-construction.
(blueprint: lem-pc-s3-alternating-cech-sheaf-terms).

Proof: The intersection presheaf with sections G(V intersect W) is isomorphic to the
underlying presheaf of the extension from the over site of W: categorical products of
opens are their infima. These comparison maps are restrictions along the canonical
intersection isomorphisms and are O(V)-linear. Sheafification of that presheaf is the
extension sheaf, by the sheafification counit. The over-site equivalence identifies
G.over W with G restricted to W.toScheme. Uniqueness of right adjoints identifies
extension from the over site with scheme module pushforward. Finally module
sheafification is additive and a left adjoint, so it preserves finite biproducts
and hence finite products. Take the product of the preceding isomorphisms over the
increasing tuples. Empty tuple types give empty products on both sides. No covering,
affineness or quasi-coherence hypothesis is needed. -/
theorem alternatingCechSheafComplex_terms
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (k : ℕ) :
    Nonempty ((alternatingCechSheafComplex U G).X k ≅
      ∏ᶜ fun t : Fin (k + 1) ↪o Fin r ↦
        (Scheme.Modules.pushforward (alternatingCechIntersection U t).ι).obj
          (G.restrict (alternatingCechIntersection U t).ι)) := by
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let : L.Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  let : L.IsLeftAdjoint := inferInstance
  refine ⟨PreservesProduct.iso L (fun t : Fin (k + 1) ↪o Fin r ↦
    cechCapModule G (alternatingCechIntersection U t)) ≪≫ ?_⟩
  exact Pi.mapIso fun t ↦ capSheafificationIsoPushforward G (alternatingCechIntersection U t)

end AlgebraicGeometry
