/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence

/-!
# Pasting of the normalized strict-tower inverse-image square

Source: Stacks, Tag 07A7; the pullback composition coherence calculation used in
(blueprint: lem-cbc-strict-tower-pullback-square-pasting).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem gCompEq_refl {V W S : Scheme.{u}} (f : V ⟶ W) (k : W ⟶ S) :
    gComp B f k = gCompEq B f k (f ≫ k) rfl := by
  unfold gCompEq
  exact (Iso.refl_trans _).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem squareG_eq {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    (w : k ≫ p = r ≫ i) :
    squareG B k r p i w =
      (gCompEq B r i (k ≫ p) w.symm).symm ≪≫ gCompEq B k p (k ≫ p) rfl := by
  unfold squareG gCompEq
  exact normalizeIsoSquare (gComp B r i) (gComp B k p) (congrArg (G B) w.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The inverse-image comparisons of successive commutative squares paste.
Source: Stacks, Tag 07A7, and pullback-composition coherence
(blueprint: lem-cbc-strict-tower-pullback-square-pasting).
Proof: expand each square comparison into the two inverse-image compositors and
the equality of the composite scheme maps. The associativity law for these
compositors identifies both paths with the same comparison from the inverse image
of the composite map to three successive inverse images. This law holds on module
sheaves because the direct-image compositors are restriction along the unique
pullback pasting isomorphisms; their conjugate pullback compositors inherit it.
Whiskering to strict towers and exact derived localization preserve the equation.
No openness or cartesianness is required. -/
theorem squareG_pasting_inv {U U₁ U₂ X X₁ X₂ : Scheme.{u}}
    (j : U ⟶ X) (j₁ : U₁ ⟶ X₁) (j₂ : U₂ ⟶ X₂)
    (g : X₁ ⟶ X) (h : X₂ ⟶ X₁) (a : U₁ ⟶ U) (b : U₂ ⟶ U₁)
    (w₁ : a ≫ j = j₁ ≫ g) (w₂ : b ≫ j₁ = j₂ ≫ h)
    (w : (b ≫ a) ≫ j = j₂ ≫ (h ≫ g)) (N : Derived B X) :
    (gComp B b a).hom.app ((G B j).obj N) ≫
        (G B b).map ((squareG B a j₁ j g w₁).inv.app N) ≫
        (squareG B b j₂ j₁ h w₂).inv.app ((G B g).obj N) =
      (squareG B (b ≫ a) j₂ j (h ≫ g) w).inv.app N ≫
        (G B j₂).map ((gComp B h g).hom.app N) := by
  rw [gCompEq_refl B b a, gCompEq_refl B h g,
    squareG_eq B a j₁ j g w₁, squareG_eq B b j₂ j₁ h w₂,
    squareG_eq B (b ≫ a) j₂ j (h ≫ g) w]
  simp only [Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have first := NatTrans.congr_app (congrArg Iso.hom
    (gCompEq_coherence B b a j (b ≫ a) (a ≫ j) ((b ≫ a) ≫ j)
      rfl rfl rfl (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at first
  have first' := rearrange_square _ _ _ _ first.symm
  rw [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at first'
  rw [reassoc_of% first']
  have second := NatTrans.congr_app (congrArg Iso.hom
    (gCompEq_coherence B b j₁ g (b ≫ j₁) (a ≫ j) ((b ≫ a) ≫ j) rfl w₁.symm
      (by rw [Category.assoc, ← w₁, ← Category.assoc]) (Category.assoc b a j).symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at second
  have second' := rearrange_square _ _ _ _ second
  simp only [NatIso.inv_hom_app] at second'
  rw [reassoc_of% second']
  rw [Iso.hom_inv_id_app_assoc]
  have key := NatTrans.congr_app (congrArg Iso.hom
    (gCompEq_coherence B j₂ h g (b ≫ j₁) (h ≫ g) ((b ≫ a) ≫ j)
      w₂.symm rfl (by rw [Category.assoc, ← w₁, ← Category.assoc]) w.symm)) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at key
  rw [← key]

end AlgebraicGeometry.ProEtale.StrictTower
