/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Composition of inverse images on single complexes

Source: Stacks Project, Tag 09Z1, derived-adjunction coherence elaboration.
(blueprint: lem-sbc-abelian-pullback-single-composition).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The composition comparison of exact derived pullbacks agrees on single complexes
with the underived comparison. Source: Stacks Project, Tag 09Z1, compatibility of
comparison morphisms, and the levelwise construction of exact derived inverse image.
(blueprint: lem-sbc-abelian-pullback-single-composition).

Proof: First transport along w, reducing h' to a ≫ h. Include the bounded below
categories in the unbounded categories. The single-functor comparisons are induced
by the termwise single-complex comparisons. Compute the composition comparison on
that single complex using the localization factorization of both exact functors.
The two termwise comparisons agree in degree zero with upperStarComp and are
identities between zero objects in every other degree. Their equality passes to
localization and then back through the fully faithful bounded below inclusion. -/
theorem abelianPullbackSingleComposition {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (A : Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (((h')^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app A) ≫
        (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ =
      (eqToIso (congrArg
          (fun t : Y' ⟶ S => ((t)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
          w.symm)).hom.app ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫
        (upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom.app _ ≫
        D+((a)^*[AddCommGrpCat.{v + 1}]).map
          ((((h)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A)
    := by
  subst h'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← cancel_mono
    ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
      (((h)^*[AddCommGrpCat.{v + 1}]).obj A))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  symm
  rw [upperStarPlusComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  erw [Category.comp_id]
  rw [Functor.plus_single_comp
    (h)^*[AddCommGrpCat.{v + 1}] (a)^*[AddCommGrpCat.{v + 1}] 0 A,
    Functor.plus_single_natIso
      (upperStarComp AddCommGrpCat.{v + 1} a h (a ≫ h) rfl) 0 A]

end AlgebraicGeometry.Etale
