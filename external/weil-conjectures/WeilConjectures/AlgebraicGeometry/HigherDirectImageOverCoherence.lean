/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions


import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionIdentity
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionComposition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Functoriality of higher-image transitions

Source: Stacks Project, Tag 09Z1 and Tag 03Q8.
(blueprint: sbc-lem-higher-image-over-transition-coherence).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_comparison_cocycle
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (wgh : gh = g ≫ h) (wfgh : fgh = f ≫ gh)
    (G : Sheaf W.smallEtaleTopology A) :
    (upperStarComp A (f ≫ g) h fgh
        (by rw [wfgh, wgh, Category.assoc])).inv.app G =
    (upperStarComp A f g).hom.app (((h)^*[A]).obj G) ≫
      ((f)^*[A]).map ((upperStarComp A g h gh wgh).inv.app G) ≫
        (upperStarComp A f gh fgh wfgh).inv.app G := by
  apply (Iso.inv_comp_eq ((upperStarComp A f g).app _)).mp
  subst gh
  subst fgh
  have hc := congrArg Iso.inv (upperStarComp_assoc A f g h)
  simpa only [Iso.app_inv, Functor.comp_obj, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] using (NatTrans.congr_app hc G).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_comparison_identity
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {X W : Scheme.{u}}
    (h : X ⟶ W) (G : Sheaf W.smallEtaleTopology A) :
    (upperStarComp A (𝟙 X) h h (Category.id_comp h).symm).inv.app G =
      (upperStarId A X).hom.app (((h)^*[A]).obj G) := by
  rw [upperStarComp_id_left]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem over_map_identity
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (U : Over W) : higherDirectImageOverMap Λ k G q (𝟙 U) = 𝟙 _ := by
  have he : (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 U.left) U.hom U.hom
      (Over.w (𝟙 U)).symm).inv.app G =
      (upperStarId (ModuleCat.{u + 1} Λ) U.left).hom.app
        (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) := by
    exact pullback_comparison_identity (ModuleCat.{u + 1} Λ) U.hom G
  exact (congrArg (fun f ↦ higherDirectImageTransition Λ (𝟙 U.left)
    (U.hom ≫ k) (U.hom ≫ k) (Category.id_comp _) q _ ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f))) he).trans
    (higher_direct_image_transition_identity Λ (U.hom ≫ k) q _)

set_option backward.isDefEq.respectTransparency false in
private theorem over_map_composition
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {U V Z : Over W} (φ : U ⟶ V) (ψ : V ⟶ Z) :
    higherDirectImageOverMap Λ k G q (φ ≫ ψ) =
      higherDirectImageOverMap Λ k G q ψ ≫ higherDirectImageOverMap Λ k G q φ := by
  let eφ := (upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
    (Over.w φ).symm).inv.app G
  let eψ := (upperStarComp (ModuleCat.{u + 1} Λ) ψ.left Z.hom V.hom
    (Over.w ψ).symm).inv.app G
  let ec := (upperStarComp (ModuleCat.{u + 1} Λ) (φ.left ≫ ψ.left) Z.hom U.hom
    (Over.w (φ ≫ ψ)).symm).inv.app G
  let wφ : φ.left ≫ (V.hom ≫ k) = U.hom ≫ k :=
    by rw [← Category.assoc, Over.w]
  let wψ : ψ.left ≫ (Z.hom ≫ k) = V.hom ≫ k :=
    by rw [← Category.assoc, Over.w]
  have he : ec = (upperStarComp (ModuleCat.{u + 1} Λ) φ.left ψ.left).hom.app
      (((Z.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
        ((φ.left)^*[ModuleCat.{u + 1} Λ]).map eψ ≫ eφ := by
    exact pullback_comparison_cocycle (ModuleCat.{u + 1} Λ)
      φ.left ψ.left Z.hom V.hom U.hom (Over.w ψ).symm (Over.w φ).symm G
  have ht := higher_direct_image_transition_composition Λ ψ.left φ.left
    (Z.hom ≫ k) (V.hom ≫ k) (U.hom ≫ k) wψ wφ q
    (((Z.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
    (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
    (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) eψ eφ
  exact (congrArg (fun f ↦ higherDirectImageTransition Λ (φ.left ≫ ψ.left)
    (Z.hom ≫ k) (U.hom ≫ k) (by rw [Category.assoc, wψ, wφ]) q _ ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f))) he).trans ht

/-- Canonical higher-image transitions are contravariantly functorial on schemes over W.
The maps are the canonical unit/composition/counit transitions of the source library.
Source: Stacks Project, Tag 09Z1, canonical comparison maps; Tag 03Q8.
(blueprint: sbc-lem-higher-image-over-transition-coherence).

Proof: Use the triangle identities for derived inverse/direct-image adjunctions to
cancel the unit and counit for an identity. For two composable arrows, expand both
units and counits using the composition adjunction. Naturality moves the intervening
unit past the counit, and the triangle identity cancels them. Associativity of the
inverse-image composition isomorphisms identifies the remaining factors with the
single transition for the composite. Apply homology and use the naturality and
composition coherence of inverse image on complexes concentrated in degree zero.
The final inverse-image identifications of G compose by upper-star coherence. -/
theorem higher_image_over_transition_coherence
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    : (∀ U : Over W, higherDirectImageOverMap Λ k G q (𝟙 U) = 𝟙 _) ∧
      (∀ {U V Z : Over W} (φ : U ⟶ V) (ψ : V ⟶ Z),
        higherDirectImageOverMap Λ k G q (φ ≫ ψ) =
          higherDirectImageOverMap Λ k G q ψ ≫ higherDirectImageOverMap Λ k G q φ) := by
  exact ⟨over_map_identity Λ k G q, fun φ ψ ↦ over_map_composition Λ k G q φ ψ⟩

end AlgebraicGeometry.Etale
