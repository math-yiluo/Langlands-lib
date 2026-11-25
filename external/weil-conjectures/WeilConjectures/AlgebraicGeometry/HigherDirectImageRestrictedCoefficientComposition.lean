/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Composition of the restricted single-complex coefficient maps

Source: Stacks Project, Tags 03CB and 09Z1, canonical comparison maps.
(blueprint: lem-sbc-restricted-single-coefficient-composition).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The degree-zero coefficient identification respects two restrictions.

Source: Stacks Project, Tags 03CB and 09Z1; the coefficient factor of
lem-sbc-higher-image-raw-pullback-composition-formula, step 2.
(blueprint: lem-sbc-restricted-single-coefficient-composition).

Proof: Expand each coefficient map as the single-functor comparison followed by
single of the inverse underived composition comparison. Functoriality distributes
the outer derived inverse image over the two factors of the inner coefficient map.
Naturality of the outer single-functor comparison moves the underived coefficient
identification past it. Apply upperStarPlusComp_single to combine the two single
comparisons. Associativity of upperStarComp for f.left, g.left, C.hom identifies
the two successive underived inverse comparisons with that for (f ≫ g).left and
C.hom; use Over.w f and Over.w g to identify their diagonal maps. Cancel the
intermediate inverse and forward comparisons and reassociate. This is solely a
coefficient identity: it involves no base S, test object, cohomology class, or shift.
Identity arrows and the zero sheaf satisfy the same coherence identities. -/
theorem higherDirectImageRestrictedCoefficient_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) :
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) f.left g.left).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((C.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) ≫
      D+((f.left)^*[ModuleCat.{u + 1} Λ]).map
        ((((g.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp (ModuleCat.{u + 1} Λ) g.left C.hom B.hom
              (Over.w g).symm).inv.app G)) ≫
      (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G) =
    ((((f ≫ g).left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) (f ≫ g).left C.hom A.hom
          (Over.w (f ≫ g)).symm).inv.app G) := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  have hn :=
    (((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality
    ((upperStarComp (ModuleCat.{u + 1} Λ) g.left C.hom B.hom
      (Over.w g).symm).inv.app G)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have key := upperStarComp_hom_app_map_upperStarComp_inv_app
    (ModuleCat.{u + 1} Λ) f.left g.left C.hom (f ≫ g).left B.hom A.hom
    (Over.comp_left _ _ _ f g) (Over.w g).symm (Over.w (f ≫ g)).symm G
  have hu :
      ((f.left)^*[ModuleCat.{u + 1} Λ]).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) g.left C.hom B.hom
            (Over.w g).symm).inv.app G) ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G =
      (upperStarComp (ModuleCat.{u + 1} Λ) f.left g.left (f ≫ g).left
          (Over.comp_left _ _ _ f g)).inv.app
            (((C.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ≫
        (upperStarComp (ModuleCat.{u + 1} Λ) (f ≫ g).left C.hom A.hom
          (Over.w (f ≫ g)).symm).inv.app G := by
    apply (cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ)
      f.left g.left (f ≫ g).left (Over.comp_left _ _ _ f g)).hom.app
        (((C.hom)^*[ModuleCat.{u + 1} Λ]).obj G))).mp
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    rw [key]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← Functor.map_comp, hu, Functor.map_comp]
  simp only [Over.comp_left] at *
  rw [reassoc_of% (upperStarPlusComp_single Λ f.left g.left
    (((C.hom)^*[ModuleCat.{u + 1} Λ]).obj G))]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end AlgebraicGeometry.Etale
