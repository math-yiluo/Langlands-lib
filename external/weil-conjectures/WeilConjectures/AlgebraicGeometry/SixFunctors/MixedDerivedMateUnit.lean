/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Unit normalization of a mixed derived mate

## References

* Stacks Project, Tags 0F7B and 0D6E
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma comp_homotopy_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma square_factors
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    (T : C ⥤ D) (L' : D ⥤ V) (L : C ⥤ E) (O : E ⥤ V)
    [T.Additive] [L'.Additive] [L.Additive] [O.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (e : T ⋙ L' ≅ L ⋙ O) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        O.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        O.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L')) (.up ℤ)).hom.app K ≫
            (e.hom.mapHomotopyCategory (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ O)) (.up ℤ)).inv.app K) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj e K
  apply (cancel_epi
    (L'.mapDerivedCategoryFactorsh.inv.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
      L'.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.inv.app K))).1
  simp only [Category.assoc, ← L'.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [L'.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact h

/-- The mate of an exact derived square carries the source right-derived unit to the
ordinary homotopy mate followed by the target unit. Expand the derived mate as unit,
square and counit; use their factorization identities and naturality. On complex
representatives the remaining equality is the ordinary mate formula degree by degree. -/
theorem mixedDerivedMateUnit
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    [Abelian.HasKInjectiveResolutions E] [Abelian.HasKInjectiveResolutions V]
    (T : C ⥤ D) (L' : D ⥤ V) (L : C ⥤ E) (O : E ⥤ V)
    (R : E ⥤ C) (P : V ⥤ D)
    [T.Additive] [L'.Additive] [L.Additive] [O.Additive] [R.Additive] [P.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (adj : L ⊣ R) (adj' : L' ⊣ P) (e : T ⋙ L' ≅ L ⋙ O)
    (β : T.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ O.mapDerivedCategory)
    (hβ : (Functor.mapDerivedCategorySquareIso e).hom = β)
    (K : HomotopyCategory E (.up ℤ)) :
    T.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ β)).app
          (DerivedCategory.Qh.obj K) ≫
        P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
      T.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ T)) (.up ℤ)).hom.app K ≫
            ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).mapHomotopyCategory
              (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K) ≫
        P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) := by
  subst β
  let KH := (R.mapHomotopyCategory (.up ℤ)).obj K
  let b := Functor.mapDerivedCategorySquareIso e
  have hc : L.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj K) =
      L.mapDerivedCategoryFactorsh.hom.app KH ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso E (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K
  have hu := (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
    P.rightDerivedFunctorUnit ((T.mapHomotopyCategory (.up ℤ)).obj KH)
  have hm : (adj'.mapHomotopyCategory (.up ℤ)).unit.app
        ((T.mapHomotopyCategory (.up ℤ)).obj KH) ≫
      (P.mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L')) (.up ℤ)).hom.app KH ≫
          (e.hom.mapHomotopyCategory (.up ℤ)).app KH ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ O)) (.up ℤ)).inv.app KH ≫
          (O.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ T)) (.up ℤ)).hom.app K ≫
        ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).mapHomotopyCategory
          (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    dsimp only [KH]
    erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
      Adjunction.mapHomotopyCategory_counit_app_quotient]
    change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ =
        (HomotopyCategory.quotient D (.up ℤ)).map _
    simp only [← Functor.map_comp]
    congr 1
    ext n
    change adj'.unit.app (T.obj (R.obj (J.X n))) ≫
      P.map ((𝟙 _) ≫ e.hom.app (R.obj (J.X n)) ≫ (𝟙 _) ≫
        O.map (adj.counit.app (J.X n))) =
      (𝟙 _) ≫ (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).app
        (J.X n) ≫ (𝟙 _)
    simp [mateEquiv_apply]
  have hmate :
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ b.hom)).app (DerivedCategory.Qh.obj K) =
      adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
        P.rightDerivedFunctor.map (b.hom.app _ ≫
          O.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app _)) := by
    simp [mateEquiv_apply]
  rw [hmate]
  change T.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫
        P.rightDerivedFunctor.map (b.hom.app _ ≫
          O.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app _))) ≫
      P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) = _
  simp only [Category.assoc]
  erw [reassoc_of% (adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (T.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K)))]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map]
  simp only [Category.assoc, ← P.rightDerivedFunctor.map_comp]
  erw [reassoc_of% b.hom.naturality (R.rightDerivedFunctorUnit.app K)]
  rw [← O.mapDerivedCategory.map_comp_assoc, hc]
  have ho := O.mapDerivedCategoryFactorsh.hom.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at ho
  rw [O.mapDerivedCategory.map_comp, Category.assoc, ho]
  rw [reassoc_of% (square_factors T L' L O e KH)]
  rw [P.rightDerivedFunctor.map_comp, P.rightDerivedFunctor.map_comp,
    ← reassoc_of% adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
      (T.mapDerivedCategoryFactorsh.hom.app KH)]
  erw [reassoc_of% hu]
  rw [← DerivedCategory.Qh.map_comp]
  have hp := P.rightDerivedFunctorUnit.naturality
    (((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L')) (.up ℤ)).hom.app KH ≫
      (e.hom.mapHomotopyCategory (.up ℤ)).app KH ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ O)) (.up ℤ)).inv.app KH) ≫
      (O.mapHomotopyCategory (.up ℤ)).map
        ((adj.mapHomotopyCategory (.up ℤ)).counit.app K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hp
  rw [← hp]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  simp only [Category.assoc]
  rw [hm]
  rfl

end AlgebraicGeometry.Etale
