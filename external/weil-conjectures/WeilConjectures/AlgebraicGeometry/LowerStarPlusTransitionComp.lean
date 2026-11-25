/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition

import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Composition of derived direct-image transitions

Source: Stacks Tag 09Z1, canonical restriction maps, and Mathlib's mate calculus.
(blueprint: lem-sbc-lower-star-plus-transition-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Derived direct-image transitions compose after the pullback composition comparison.

Source: Stacks Tag 09Z1, restriction maps for higher direct images; the mate calculation
is Mathlib `mateEquiv_vcomp`, specialized to identity functors on the common base.
(blueprint: lem-sbc-lower-star-plus-transition-comp)

Proof: the transition for a triangle is the adjunct of its pullback comparison followed
by pullback of the counit. Apply the inverse hom-set equivalence for the adjunction
D(h₁)^* ⊣ R(h₁)_* to the desired equality. Naturality of that equivalence and of the
comparison for a₁ moves the first transition inside D(a₁)^*. The counit for h₂ followed
by its own adjunct cancels by a triangle identity. The resulting composite is the
comparison for (a₁,h₂), then D(a₁)^* of the comparison for (a₂,h), then
D(a₁)^*D(a₂)^* of the counit for h, followed by the inverse comparison for a₁,a₂.
Associativity `upperStarCompDerivedPlus_assoc` identifies the first two comparisons
with the comparison for (a₁ ≫ a₂,h) followed by the comparison for a₁,a₂.
Naturality of the latter moves the counit past it; its inverse cancels. What remains
is exactly the adjunct defining the composite transition. Injectivity of the hom-set
equivalence proves the equality. Transport along wh₂ and wh₁ uses eqToIso, with proof
irrelevance ensuring independence of the chosen witnesses. No cartesianness, properness,
or degree bound is used. Identity triangles satisfy the same proof by the unit laws,
and the zero complex gives the equality of zero maps.
-/
theorem Etale.lowerStarPlusTransition_comp_target
    {X Y Y₁ Y₂ : Scheme.{u}} (h : Y ⟶ X)
    (a₂ : Y₂ ⟶ Y) (h₂ : Y₂ ⟶ X) (wh₂ : a₂ ≫ h = h₂)
    (a₁ : Y₁ ⟶ Y₂) (h₁ : Y₁ ⟶ X) (wh₁ : a₁ ≫ h₂ = h₁)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusTransition Λ a₂ h h₂ wh₂ K ≫
        Etale.lowerStarPlusTransition Λ a₁ h₂ h₁ wh₁
          (D+((a₂)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
        R+((h₁)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app K) =
      Etale.lowerStarPlusTransition Λ (a₁ ≫ a₂) h h₁
        (by rw [Category.assoc, wh₂, wh₁]) K := by
  subst h₂
  subst h₁
  let A := ModuleCat.{u + 1} Λ
  let adj₀ := Etale.derivedUpperStarLowerStarAdjunctionPlus A h
  let adj₂ := Etale.derivedUpperStarLowerStarAdjunctionPlus A (a₂ ≫ h)
  let adj₁ := Etale.derivedUpperStarLowerStarAdjunctionPlus A (a₁ ≫ a₂ ≫ h)
  let c₂ := Etale.upperStarPlusComp A a₂ h
  let c₁ := Iso.refl D+((a₁ ≫ a₂ ≫ h)^*[A]) ≪≫
    Etale.upperStarPlusComp A a₁ (a₂ ≫ h)
  let t₂ := Etale.lowerStarPlusTransition Λ a₂ h (a₂ ≫ h) rfl K
  let f₂ := c₂.hom.app (R+((h)_*[A]).obj K) ≫
    D+((a₂)^*[A]).map (adj₀.counit.app K)
  have ht₂ : (adj₂.homEquiv (R+((h)_*[A]).obj K)
      (D+((a₂)^*[A]).obj K)).symm t₂ = f₂ := by
    have he : t₂ = (adj₂.homEquiv (R+((h)_*[A]).obj K)
        (D+((a₂)^*[A]).obj K)) f₂ := by
      simp only [t₂, Etale.lowerStarPlusTransition, eqToIso_refl, Iso.refl_trans]
      rfl
    rw [he]
    exact Equiv.symm_apply_apply _ f₂
  let c := eqToIso (show D+((a₁ ≫ a₂ ≫ h)^*[A]) =
      D+(((a₁ ≫ a₂) ≫ h)^*[A]) by rw [Category.assoc]) ≪≫
    Etale.upperStarPlusComp A (a₁ ≫ a₂) h
  change D+((a₂ ≫ h)^*[A]).map t₂ ≫ adj₂.counit.app _ = f₂ at ht₂
  apply (adj₁.homEquiv _ _).symm.injective
  rw [← Category.assoc t₂, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  change (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂ ≫
      (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
        (c₁.hom.app _ ≫ D+((a₁)^*[A]).map (adj₂.counit.app _)))) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
    (adj₁.homEquiv _ _).symm ((adj₁.homEquiv _ _)
      (c.hom.app _ ≫ D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hn := c₁.hom.naturality t₂
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc (D+((a₁ ≫ a₂ ≫ h)^*[A]).map t₂), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ht₂]
  dsimp only [f₂]
  rw [Functor.map_comp]
  have ha := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc A a₁ a₂ h
    (a₁ ≫ a₂) (a₂ ≫ h) (a₁ ≫ a₂ ≫ h) rfl rfl (Category.assoc _ _ _).symm)
    (R+((h)_*[A]).obj K)
  simp only [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans, eqToIso_refl,
    Iso.refl_trans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at ha
  have ha' : c₁.hom.app (R+((h)_*[A]).obj K) ≫
      D+((a₁)^*[A]).map (c₂.hom.app _) =
      c.hom.app _ ≫ (Etale.upperStarPlusComp A a₁ a₂).hom.app _ := by
    simpa only [c₁, c₂, c, eqToIso_refl, Iso.refl_trans] using ha
  simp only [Category.assoc]
  rw [← Category.assoc (c₁.hom.app _), ha']
  have hn' := (Etale.upperStarPlusComp A a₁ a₂).inv.naturality (adj₀.counit.app K)
  dsimp only [Functor.comp_map] at hn'
  change D+((a₁)^*[A]).map (D+((a₂)^*[A]).map (adj₀.counit.app K)) ≫
      (Etale.upperStarPlusComp A a₁ a₂).inv.app K =
      (Etale.upperStarPlusComp A a₁ a₂).inv.app
        (D+((h)^*[A]).obj (R+((h)_*[A]).obj K)) ≫
      D+((a₁ ≫ a₂)^*[A]).map (adj₀.counit.app K) at hn'
  simp only [Category.assoc]
  rw [hn']
  simp only [← Category.assoc, Iso.hom_inv_id_app]
  change (c.hom.app (R+((h)_*[A]).obj K) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]

end AlgebraicGeometry
