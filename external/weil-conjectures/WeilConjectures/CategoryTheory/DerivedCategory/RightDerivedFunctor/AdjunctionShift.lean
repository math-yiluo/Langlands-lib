/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# The unit of a right derived functor commutes with the shifts

Let `L ⊣ R` be an adjunction of additive functors between abelian categories, with `L` exact,
so that `L.mapDerivedCategory ⊣ R.rightDerivedFunctor`
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`).

* `CategoryTheory.Adjunction.commShift_mapHomotopyCategory_counit`: the counit of the induced
  adjunction on homotopy categories commutes with the shifts.
* `CategoryTheory.Adjunction.commShift_rightDerivedFunctorUnit`: if `R.rightDerivedFunctor` is
  given a shift structure for which the derived adjunction commutes with the shifts (for
  instance the one transported from `L.mapDerivedCategory` by
  `CategoryTheory.Adjunction.rightAdjointCommShift`), then the unit
  `R.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ R.rightDerivedFunctor` commutes with the shifts.
* `CategoryTheory.NatTrans.CommShift.of_comp_whiskerLeft_Qh`: a natural transformation
  `τ : S ⟶ G` out of a functor `S : D(C) ⥤ E` commutes with the shifts as soon as `β ≫ Qh τ`
  does, for some `β : F ⟶ Qh ⋙ S` commuting with the shifts which is an isomorphism on
  K-injective complexes.
-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)

/-- The counit of the adjunction induced on cochain complexes commutes with the shifts. -/
instance commShift_mapHomologicalComplex_counit :
    NatTrans.CommShift (adj.mapHomologicalComplex (.up ℤ)).counit ℤ where
  shift_comm n := by
    ext K i
    dsimp [mapHomologicalComplex]
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      HomologicalComplex.id_f, CochainComplex.shiftFunctor_obj_X', Category.comp_id]
    rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- The counit of the adjunction induced on homotopy categories commutes with the shifts. -/
instance commShift_mapHomotopyCategory_counit :
    NatTrans.CommShift (adj.mapHomotopyCategory (.up ℤ)).counit ℤ := by
  have : Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ))
      (adj.mapHomotopyCategory (.up ℤ)).counit =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (R.mapHomotopyCategoryFactors (.up ℤ)).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (R.mapHomologicalComplex (.up ℤ))
          (L.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (adj.mapHomologicalComplex (.up ℤ)).counit
          (HomotopyCategory.quotient D (.up ℤ)) ≫
        (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by
    ext K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      mapHomotopyCategory_counit_app_quotient]
    simp only [Functor.mapHomotopyCategoryFactors]
    erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.comp_id,
      Category.id_comp, Category.comp_id]
    erw [Quotient.lift.isLift_hom, CategoryTheory.Functor.map_id, Category.id_comp]
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient D (.up ℤ))
      (adj.mapHomotopyCategory (.up ℤ)).counit) ℤ := by
    rw [this]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient D (.up ℤ))
    (fun X ↦ ⟨_, 𝟙 _, (HomotopyCategory.quotient_obj_surjective X).choose_spec ▸ inferInstance⟩)

section Derived

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The unit `R.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ R.rightDerivedFunctor` is the adjoint of
`L(Qh R X) ≅ Qh(L R X) ⟶ Qh X` for the derived adjunction. -/
lemma rightDerivedFunctorUnit_app (X : HomotopyCategory D (.up ℤ)) :
    R.rightDerivedFunctorUnit.app X =
      (adj.mapDerivedCategoryRightDerivedAdjunction).unit.app
          (DerivedCategory.Qh.obj ((R.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app _ ≫
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app X)) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit X
  rw [← h, Functor.map_comp]
  erw [Adjunction.unit_naturality_assoc]
  erw [(adj.mapDerivedCategoryRightDerivedAdjunction).right_triangle_components, Category.comp_id]

/-- The unit of `R.rightDerivedFunctor` commutes with the shifts, for a shift structure on
`R.rightDerivedFunctor` for which the derived adjunction commutes with the shifts. -/
lemma commShift_rightDerivedFunctorUnit [R.rightDerivedFunctor.CommShift ℤ]
    [(adj.mapDerivedCategoryRightDerivedAdjunction).CommShift ℤ] :
    NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := by
  let β : R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R.rightDerivedFunctor :=
    (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
        (adj.mapDerivedCategoryRightDerivedAdjunction).unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (R.mapHomotopyCategory (.up ℤ)) L.mapDerivedCategoryFactorsh.hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (adj.mapHomotopyCategory (.up ℤ)).counit DerivedCategory.Qh ≫
        (Functor.leftUnitor _).hom) R.rightDerivedFunctor
  have hβ : R.rightDerivedFunctorUnit = β := by
    ext X
    rw [rightDerivedFunctorUnit_app adj]
    simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Category.id_comp, Functor.map_comp, Functor.comp_obj]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hβ]
  infer_instance

end Derived

end Adjunction

namespace NatTrans.CommShift

variable {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] [Category E] [HasShift E ℤ]
  {F' : HomotopyCategory C (.up ℤ) ⥤ E} {S G : DerivedCategory C ⥤ E}
  [F'.CommShift ℤ] [S.CommShift ℤ] [G.CommShift ℤ]

/-- A natural transformation `τ : S ⟶ G` out of a functor on the derived category commutes
with the shifts as soon as `β ≫ Qh τ` does, for some `β : F' ⟶ Qh ⋙ S` which commutes with the
shifts and is an isomorphism on K-injective complexes: K-injective complexes represent all
objects of the derived category. -/
lemma of_comp_whiskerLeft_Qh (β : F' ⟶ DerivedCategory.Qh ⋙ S) [NatTrans.CommShift β ℤ]
    [IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal) β)]
    (τ : S ⟶ G) [NatTrans.CommShift (β ≫ Functor.whiskerLeft DerivedCategory.Qh τ) ℤ] :
    NatTrans.CommShift τ ℤ := by
  let ι := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  have e : Functor.whiskerLeft (ι ⋙ DerivedCategory.Qh) τ =
      (Functor.associator _ _ _).hom ≫ inv (Functor.whiskerLeft ι β) ≫
        Functor.whiskerLeft ι (β ≫ Functor.whiskerLeft DerivedCategory.Qh τ) ≫
        (Functor.associator _ _ _).inv := by
    simp only [Functor.whiskerLeft_comp, Functor.whiskerLeft_twice, assoc, Iso.hom_inv_id,
      comp_id, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have : NatTrans.CommShift (inv (Functor.whiskerLeft ι β)) ℤ :=
    NatTrans.CommShift.of_isIso _ ℤ
  have : NatTrans.CommShift (Functor.whiskerLeft (ι ⋙ DerivedCategory.Qh) τ) ℤ := by
    rw [e]; infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (ι ⋙ DerivedCategory.Qh)
    (fun M ↦ ⟨_, ((ι ⋙ DerivedCategory.Qh).objObjPreimageIso M).inv, inferInstance⟩)

end NatTrans.CommShift

namespace Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [F.rightDerivedFunctor.CommShift ℤ] [G.rightDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift F.rightDerivedFunctorUnit ℤ] [NatTrans.CommShift G.rightDerivedFunctorUnit ℤ]

instance commShift_rightDerivedFunctorCompUnit :
    NatTrans.CommShift (rightDerivedFunctorCompUnit F G) ℤ := by
  dsimp only [rightDerivedFunctorCompUnit]
  have : NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℤ)).inv ℤ := NatTrans.CommShift.of_iso_inv _ ℤ
  infer_instance

/-- The composition isomorphism `RF ⋙ RG ≅ RH` of total right derived functors commutes with
the shifts, for shift structures on the derived functors with which the units commute. -/
lemma commShift_rightDerivedFunctorCompIso'_hom {H : C ⥤ E} [H.Additive]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) [H.rightDerivedFunctor.CommShift ℤ]
    [NatTrans.CommShift H.rightDerivedFunctorUnit ℤ] :
    NatTrans.CommShift (rightDerivedFunctorCompIso' F G e).hom ℤ := by
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      (rightDerivedFunctorCompUnit F G)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ ?_)
    obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    change IsIso ((rightDerivedFunctorCompUnit F G).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
    have h₁ : IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := inferInstance
    have h₂ : IsIso (G.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := inferInstance
    have h₂' : IsIso (G.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K).as))) := h₂
    dsimp [rightDerivedFunctorCompUnit]
    infer_instance
  have e₁ : rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (rightDerivedFunctorCompIso' F G e).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ H.rightDerivedFunctorUnit := by
    simp only [rightDerivedFunctorCompIso', rightDerivedFunctorCompIso, Iso.trans_hom,
      Iso.symm_hom, rightDerivedNatIso_inv, Functor.whiskerLeft_comp, ← Category.assoc,
      rightDerivedNatTrans_fac, Iso.refl_inv, Category.id_comp, rightDerivedFunctorNatIso]
    exact rightDerivedNatTrans_fac _ _ _ _ _ _
  have : NatTrans.CommShift (rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh (rightDerivedFunctorCompIso' F G e).hom) ℤ := by
    rw [e₁]; infer_instance
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh (rightDerivedFunctorCompUnit F G) _

end Functor

end CategoryTheory
