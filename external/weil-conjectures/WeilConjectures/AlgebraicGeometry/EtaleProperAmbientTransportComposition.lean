/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import all WeilConjectures.AlgebraicGeometry.DerivedCompactSupportCompositionCoherence
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube

/-! # Composition of Cartesian proper ambient transports

Source: Stacks Project, more-etale.tex, Tag 0F7C, vertical pasting.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar openImmersionLowerShriek Functor.leftDerivedFunctor
  rightDerivedLowerStarComp

private theorem compOfEq_hom
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg h).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom ≫
        eqToHom (congrArg (fun k ↦ R((k)_*[ModuleCat.{u + 1} A])) h) := by
  subst fg
  simp only [rightDerivedLowerStarCompOfEq, eqToHom_refl, Category.comp_id]

private theorem comp_assoc
    (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfull : fg ≫ h = fgh)
    (M : DerivedCategoryModule A W) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) g h gh hgh).hom.app
        (R((f)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f gh fgh
        (by rw [← hgh, ← Category.assoc, hfg, hfull])).hom.app M =
    R((h)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg hfg).hom.app M) ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) fg h fgh hfull).hom.app M := by
  subst fg
  subst gh
  rw [Category.assoc] at hfull
  subst fgh
  simpa only [compOfEq_hom, NatTrans.comp_app, eqToHom_app, eqToHom_refl,
    Category.comp_id, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] using congr_app (push_derived_assoc A f g h) M

private theorem comp_assoc_inv
    (A : Type (u + 1)) [CommRing A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfull : fg ≫ h = fgh)
    (M : DerivedCategoryModule A W) :
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) fg h fgh hfull).inv.app M ≫
      R((h)_*[ModuleCat.{u + 1} A]).map
        ((rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f g fg hfg).inv.app M) =
    (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) f gh fgh
        (by rw [← hgh, ← Category.assoc, hfg, hfull])).inv.app M ≫
      (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A) g h gh hgh).inv.app
        (R((f)_*[ModuleCat.{u + 1} A]).obj M) := by
  have hi := IsIso.inv_eq_inv.mpr (comp_assoc A f g h fg gh fgh hfg hgh hfull M)
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] using hi.symm

private theorem exchange_paste
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U₀ U₁ U₂ P₀ P₁ P₂ : Scheme.{u}}
    (e₀ : U₀ ⟶ P₀) (e₁ : U₁ ⟶ P₁) (e₂ : U₂ ⟶ P₂)
    [IsOpenImmersion e₀] [IsOpenImmersion e₁] [IsOpenImmersion e₂]
    (r₁₀ : P₁ ⟶ P₀) (r₂₁ : P₂ ⟶ P₁) [IsProper r₁₀] [IsProper r₂₁]
    (q₁₀ : U₁ ⟶ U₀) (q₂₁ : U₂ ⟶ U₁)
    (sq₁₀ : IsPullback q₁₀ e₁ e₀ r₁₀) (sq₂₁ : IsPullback q₂₁ e₂ e₁ r₂₁)
    (M : DerivedCategoryModule A U₂) :
    (openImmersionLowerShriekLowerStarExchangeIso A (sq₂₁.paste_horiz sq₁₀)).hom.app M =
      D((e₀)_!open[ModuleCat.{u + 1} A]).map
          ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) q₂₁ q₁₀).inv.app M) ≫
        (openImmersionLowerShriekLowerStarExchangeIso A sq₁₀).hom.app
          (R((q₂₁)_*[ModuleCat.{u + 1} A]).obj M) ≫
        R((r₁₀)_*[ModuleCat.{u + 1} A]).map
          ((openImmersionLowerShriekLowerStarExchangeIso A sq₂₁).hom.app M) ≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₂₁ r₁₀).hom.app
          (D((e₂)_!open[ModuleCat.{u + 1} A]).obj M) := by
  have : IsProper q₁₀ := MorphismProperty.of_isPullback sq₁₀.flip inferInstance
  have : IsProper q₂₁ := MorphismProperty.of_isPullback sq₂₁.flip inferInstance
  obtain ⟨θ, Γ, _, _, hn, hv, _⟩ := etaleProperOpenExchangeCube A
  have hp := hv e₂ e₁ e₀ q₂₁ r₂₁ q₁₀ r₁₀
    sq₂₁.toCommSq.flip sq₁₀.toCommSq.flip M
  simpa only [hn e₂ (q₂₁ ≫ q₁₀) (r₂₁ ≫ r₁₀) e₀ (sq₂₁.paste_horiz sq₁₀),
    hn e₁ q₁₀ r₁₀ e₀ sq₁₀, hn e₂ q₂₁ r₂₁ e₁ sq₂₁,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom] using hp

/-- Two Cartesian proper ambient transports compose to the transport of the rectangle.

Source: Stacks Project, more-etale.tex, Tag 0F7C, vertical proper/open exchange pasting.
(auxiliary; not a blueprint node).

Proof: use the Cartesian normalization of etaleProperOpenExchangeCube to replace the
three exchanges by the same normalized family. Its vertical pasting law expresses
the exchange of the outer rectangle as the two inner exchanges separated by the
inverse direct-image compositor on the neighborhood and the direct-image compositor
on the ambient scheme. Expand the two transports. Naturality moves the compositor
for a2,q21 through the first exchange and the compositor for r10,p0 through the
second exchange. The inverse neighborhood compositor from the pasting law cancels
the direct compositor inserted by these two graph factorizations. Associativity of
the canonical proper direct-image compositors identifies the remaining source
factor with the inverse compositor for a2,q21 q10, and the remaining target factor
with the compositor for r21 r10,p0. The functor associators only change parentheses.
This gives the displayed equality of isomorphisms. No properness of the a-maps or
p-maps is used, and no graph, compactification, or intersection appears in the law. -/
theorem etaleProperAmbientTransport_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U₀ U₁ U₂ P₀ P₁ P₂ : Scheme.{u}}
    (a₀ : X ⟶ U₀) (e₀ : U₀ ⟶ P₀) (p₀ : P₀ ⟶ Y)
    (a₁ : X ⟶ U₁) (e₁ : U₁ ⟶ P₁) (p₁ : P₁ ⟶ Y)
    (a₂ : X ⟶ U₂) (e₂ : U₂ ⟶ P₂) (p₂ : P₂ ⟶ Y)
    [IsOpenImmersion e₀] [IsOpenImmersion e₁] [IsOpenImmersion e₂]
    (r₁₀ : P₁ ⟶ P₀) (r₂₁ : P₂ ⟶ P₁) [IsProper r₁₀] [IsProper r₂₁]
    (q₁₀ : U₁ ⟶ U₀) (q₂₁ : U₂ ⟶ U₁)
    (sq₁₀ : IsPullback q₁₀ e₁ e₀ r₁₀) (sq₂₁ : IsPullback q₂₁ e₂ e₁ r₂₁)
    (ha₁₀ : a₁ ≫ q₁₀ = a₀) (ha₂₁ : a₂ ≫ q₂₁ = a₁)
    (hp₁₀ : r₁₀ ≫ p₀ = p₁) (hp₂₁ : r₂₁ ≫ p₁ = p₂) :
    etaleProperAmbientTransport A a₀ e₀ p₀ a₁ e₁ p₁ r₁₀ q₁₀ sq₁₀ ha₁₀ hp₁₀ ≪≫
        etaleProperAmbientTransport A a₁ e₁ p₁ a₂ e₂ p₂ r₂₁ q₂₁ sq₂₁ ha₂₁ hp₂₁ =
      etaleProperAmbientTransport A a₀ e₀ p₀ a₂ e₂ p₂ (r₂₁ ≫ r₁₀) (q₂₁ ≫ q₁₀)
        (sq₂₁.paste_horiz sq₁₀)
        (by rw [← Category.assoc, ha₂₁, ha₁₀])
        (by rw [Category.assoc, hp₁₀, hp₂₁]) := by
  let B := ModuleCat.{u + 1} A
  let J₀ := D((e₀)_!open[B])
  let J₁ := D((e₁)_!open[B])
  let J₂ := D((e₂)_!open[B])
  let P₀ := R((p₀)_*[B])
  let P₁ := R((p₁)_*[B])
  let c₁₀ := rightDerivedLowerStarCompOfEq B a₁ q₁₀ a₀ ha₁₀
  let c₂₁ := rightDerivedLowerStarCompOfEq B a₂ q₂₁ a₁ ha₂₁
  let c₂₀ := rightDerivedLowerStarCompOfEq B a₂ (q₂₁ ≫ q₁₀) a₀
    (by rw [← Category.assoc, ha₂₁, ha₁₀])
  let d₁₀ := rightDerivedLowerStarCompOfEq B r₁₀ p₀ p₁ hp₁₀
  let d₂₁ := rightDerivedLowerStarCompOfEq B r₂₁ p₁ p₂ hp₂₁
  let d₂₀ := rightDerivedLowerStarCompOfEq B (r₂₁ ≫ r₁₀) p₀ p₂
    (by rw [Category.assoc, hp₁₀, hp₂₁])
  let E₁₀ := openImmersionLowerShriekLowerStarExchangeIso A sq₁₀
  let E₂₁ := openImmersionLowerShriekLowerStarExchangeIso A sq₂₁
  let E₂₀ := openImmersionLowerShriekLowerStarExchangeIso A (sq₂₁.paste_horiz sq₁₀)
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [etaleProperAmbientTransport, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Category.id_comp, Category.assoc]
  change P₀.map (J₀.map (c₁₀.inv.app M)) ≫
      P₀.map (E₁₀.hom.app (R((a₁)_*[B]).obj M)) ≫
      d₁₀.hom.app (J₁.obj (R((a₁)_*[B]).obj M)) ≫
      P₁.map (J₁.map (c₂₁.inv.app M)) ≫
      P₁.map (E₂₁.hom.app (R((a₂)_*[B]).obj M)) ≫
      d₂₁.hom.app (J₂.obj (R((a₂)_*[B]).obj M)) =
    P₀.map (J₀.map (c₂₀.inv.app M)) ≫
      P₀.map (E₂₀.hom.app (R((a₂)_*[B]).obj M)) ≫
      d₂₀.hom.app (J₂.obj (R((a₂)_*[B]).obj M))
  have hn₁ := d₁₀.hom.naturality (J₁.map (c₂₁.inv.app M))
  have hn₂ := d₁₀.hom.naturality (E₂₁.hom.app (R((a₂)_*[B]).obj M))
  simp only [Functor.comp_map] at hn₁ hn₂
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂]
  have ht := comp_assoc A r₂₁ r₁₀ p₀ (r₂₁ ≫ r₁₀) p₁ p₂ rfl hp₁₀
    (by rw [Category.assoc, hp₁₀, hp₂₁]) (J₂.obj (R((a₂)_*[B]).obj M))
  rw [ht]
  change P₀.map (J₀.map (c₁₀.inv.app M)) ≫
      P₀.map (E₁₀.hom.app (R((a₁)_*[B]).obj M)) ≫
      P₀.map (R((r₁₀)_*[B]).map (J₁.map (c₂₁.inv.app M))) ≫
      P₀.map (R((r₁₀)_*[B]).map (E₂₁.hom.app (R((a₂)_*[B]).obj M))) ≫
      P₀.map ((rightDerivedLowerStarComp B r₂₁ r₁₀).hom.app
        (J₂.obj (R((a₂)_*[B]).obj M))) ≫
      d₂₀.hom.app (J₂.obj (R((a₂)_*[B]).obj M)) =
    P₀.map (J₀.map (c₂₀.inv.app M)) ≫
      P₀.map (E₂₀.hom.app (R((a₂)_*[B]).obj M)) ≫
      d₂₀.hom.app (J₂.obj (R((a₂)_*[B]).obj M))
  simp only [← P₀.map_comp_assoc]
  have hn₃ := E₁₀.hom.naturality (c₂₁.inv.app M)
  simp only [Functor.comp_map] at hn₃
  rw [← reassoc_of% hn₃]
  have hs := comp_assoc_inv A a₂ q₂₁ q₁₀ a₁ (q₂₁ ≫ q₁₀) a₀ ha₂₁ rfl ha₁₀ M
  rw [← J₀.map_comp_assoc, hs, J₀.map_comp, Category.assoc]
  have he := exchange_paste A e₀ e₁ e₂ r₁₀ r₂₁ q₁₀ q₂₁ sq₁₀ sq₂₁
    (R((a₂)_*[B]).obj M)
  exact congrArg
    (fun t ↦ P₀.map (J₀.map (c₂₀.inv.app M) ≫ t) ≫
      d₂₀.hom.app (J₂.obj (R((a₂)_*[B]).obj M))) he.symm

end AlgebraicGeometry.Etale
