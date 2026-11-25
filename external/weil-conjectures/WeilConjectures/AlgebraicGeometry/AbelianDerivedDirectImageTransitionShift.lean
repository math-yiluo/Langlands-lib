/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.DerivedAdjunctionCommShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Shift compatibility of the derived direct-image transition

Source: Stacks Project, Tag 09Z1, derived-adjunction coherence elaboration.
(blueprint: lem-sbc-abelian-derived-transition-shift).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Adjunction

/-- Transport a right-adjoint object through a comparison of left adjoints, and
then apply a coefficient morphism, using the two actual adjunctions. -/
noncomputable def transitionThrough
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    (K : D) (K' : E) (t : P.obj K ⟶ K') : R.obj K ⟶ R'.obj K' :=
  adj'.unit.app (R.obj K) ≫
    R'.map (θ.app (R.obj K) ≫ P.map (adj.counit.app K) ≫ t)

private theorem transitionThrough_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') [adj.CommShift ℤ] [adj'.CommShift ℤ]
    (P : D ⥤ E) [P.CommShift ℤ] (θ : L' ⟶ L ⋙ P) [NatTrans.CommShift θ ℤ]
    (K : D) (K' : E) (t : P.obj K ⟶ K') (n : ℤ) :
    adj.transitionThrough adj' P θ (K⟦n⟧) (K'⟦n⟧)
        ((P.commShiftIso n).hom.app K ≫ t⟦n⟧') ≫
        (R'.commShiftIso n).hom.app K' =
      (R.commShiftIso n).hom.app K ≫
        (adj.transitionThrough adj' P θ K K' t)⟦n⟧' := by
  let τ : R ⟶ P ⋙ R' :=
    R.rightUnitor.inv ≫
      Functor.whiskerLeft R adj'.unit ≫
      (Functor.associator R L' R').inv ≫
      Functor.whiskerRight (Functor.whiskerLeft R θ) R' ≫
      Functor.whiskerRight (Functor.associator R L P).inv R' ≫
      Functor.whiskerRight (Functor.whiskerRight adj.counit P) R' ≫
      Functor.whiskerRight P.leftUnitor.hom R'
  have : NatTrans.CommShift τ ℤ := by dsimp [τ]; infer_instance
  have hc := (NatTrans.shift_app_comm τ n K).symm
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_obj] at hc
  have he (M : D) (N : E) (u : P.obj M ⟶ N) :
      adj.transitionThrough adj' P θ M N u = τ.app M ≫ R'.map u := by
    simp [transitionThrough, τ, Functor.map_comp, Category.assoc]
  rw [he, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [R'.commShiftIso_hom_naturality]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (R'.map t)⟦n⟧') hc

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

private theorem plusCompatibility_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.mapDerivedCategoryPlusCompatibility.hom ℤ := by
  change NatTrans.CommShift
    (DerivedCategory.TStructure.t.plus.liftCompιIso
      (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory)
      (fun X ↦ (F.mapDerivedCategoryPlus.obj X).2)).hom ℤ
  infer_instance

private theorem plusNatIso_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryPlusNatIso e).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι =
      F.mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryNatIso e).hom ≫
          G.mapDerivedCategoryPlusCompatibility.inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [ι_map_mapDerivedCategoryPlusNatIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusNatIso e).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

private theorem plusCompIso_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    NatTrans.CommShift (mapDerivedCategoryPlusCompIso F G).hom ℤ := by
  have he : whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι =
      (F ⋙ G).mapDerivedCategoryPlusCompatibility.hom ≫
        whiskerLeft DerivedCategory.Plus.ι (mapDerivedCategoryCompIso F G).inv ≫
        (associator _ _ _).inv ≫
        whiskerRight F.mapDerivedCategoryPlusCompatibility.inv G.mapDerivedCategory ≫
        (associator _ _ _).hom ≫
        whiskerLeft F.mapDerivedCategoryPlus G.mapDerivedCategoryPlusCompatibility.inv ≫
        (associator _ _ _).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app]
    rw [ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    dsimp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
      NatTrans.id_app, Functor.comp_obj]
    erw [Category.id_comp, Functor.map_id]
    repeat erw [Category.comp_id]
  have : NatTrans.CommShift
      (whiskerRight (mapDerivedCategoryPlusCompIso F G).hom DerivedCategory.Plus.ι) ℤ := by
    rw [he]
    have := plusCompatibility_commShift F
    have := plusCompatibility_commShift G
    have := plusCompatibility_commShift (F ⋙ G)
    infer_instance
  exact NatTrans.CommShift.of_whiskerRight _ DerivedCategory.Plus.ι

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The derived transition before taking cohomology, for arbitrary complexes and a
coefficient morphism. This is an actual composite of units, comparison, and counit. -/
noncomputable def abelianDerivedDirectImageTransition {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (t : D+((a)^*[AddCommGrpCat.{v + 1}]).obj K ⟶ K') :
    R+((h)_*[AddCommGrpCat.{v + 1}]).obj K ⟶
      R+((h')_*[AddCommGrpCat.{v + 1}]).obj K' :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.transitionThrough
    (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').derivedPlus
    D+((a)^*[AddCommGrpCat.{v + 1}])
    (eqToIso (congrArg
      (fun f : Y' ⟶ S => ((f)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
      w.symm) ≪≫ upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom K K' t

/-- The derived transition commutes with integer shifts. Source: Stacks Project,
Tag 09Z1, compatibility of comparison morphisms; derived-adjunction coherence.
(blueprint: lem-sbc-abelian-derived-transition-shift).

Proof: Transport along w to reduce to h' = a ≫ h. The derived adjunction unit
commutes with shifts, as does its counit, by the existing theorem
`derivedPlus_upperStarLowerStar_commShift` for h and h'. These equalities descend
from the termwise adjunction on complexes through the localization factorization. The
composition comparison of exact pullbacks commutes with shifts because it is
induced by the termwise comparison, which commutes with shifts in every degree.
Expand the transition, apply these three identities, and use naturality of the
shift comparisons to move the coefficient morphism t through. The intermediate
shift comparisons cancel with their inverses. The two surviving comparisons are
those of Rh_* and Rh'_* displayed below. This works for arbitrary bounded below
complexes, including zero complexes, and every integer shift. -/
theorem abelianDerivedDirectImageTransition_shift {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (t : D+((a)^*[AddCommGrpCat.{v + 1}]).obj K ⟶ K') (n : ℤ) :
    abelianDerivedDirectImageTransition a h h' w (K⟦n⟧) (K'⟦n⟧)
        ((D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K ≫
          (shiftFunctor _ n).map t) ≫
        (R+((h')_*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K' =
      (R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso n).hom.app K ≫
        (shiftFunctor _ n).map (abelianDerivedDirectImageTransition a h h' w K K' t)
    := by
  subst h'
  have := derivedPlus_upperStarLowerStar_commShift h
  have := derivedPlus_upperStarLowerStar_commShift (a ≫ h)
  have : NatTrans.CommShift (upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom ℤ := by
    dsimp [upperStarPlusComp]
    have := Functor.plusNatIso_commShift (upperStarComp AddCommGrpCat.{v + 1} a h)
    have := comp_preservesFiniteLimits (h)^*[AddCommGrpCat.{v + 1}]
      (a)^*[AddCommGrpCat.{v + 1}]
    have := comp_preservesFiniteColimits (h)^*[AddCommGrpCat.{v + 1}]
      (a)^*[AddCommGrpCat.{v + 1}]
    have := Functor.plusCompIso_commShift (h)^*[AddCommGrpCat.{v + 1}]
      (a)^*[AddCommGrpCat.{v + 1}]
    infer_instance
  simpa [abelianDerivedDirectImageTransition] using
    Adjunction.transitionThrough_shift
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} (a ≫ h)).derivedPlus
      D+((a)^*[AddCommGrpCat.{v + 1}])
      (upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom K K' t n

end AlgebraicGeometry.Etale
