/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction


/-! # DerivedGlobalGermUnitFac

Source: Stacks Project, Tags 095T, 01F8 and 08J6.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] GrothendieckTopology.Point.sheafFiber_additive
noncomputable local instance instAB5OfSizeAddCommGrpCat_derivedGlobalGermUnitFac
    : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- Formal unit compatibility for a germ following two Leray comparisons.
The functors remain abstract so reduction does not unfold the small-etale constructions.
Source: the unit formulas for the library's bounded below derived comparisons. -/
private theorem derived_unit_germ_fac
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    [Abelian C] [Abelian D] [Abelian E] [Abelian A]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory A] [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
    (L : C ⥤ D) (R : D ⥤ C) (H : C ⥤ A) (H' : D ⥤ A)
    (F' : D ⥤ E) (T S : E ⥤ A)
    [L.Additive] [R.Additive] [H.Additive] [H'.Additive] [F'.Additive]
    [T.Additive] [S.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [R.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects]
    (adj : L ⊣ R) (e : R ⋙ H ≅ H') (e' : F' ⋙ T ≅ H') (γ : T ⟶ S)
    (M : HomotopyCategory.Plus C) :
    let b : H ⟶ L ⋙ F' ⋙ S :=
      (Functor.leftUnitor H).inv ≫ Functor.whiskerRight adj.unit H ≫
        (Functor.associator L R H).hom ≫ Functor.whiskerLeft L e.hom ≫
        Functor.whiskerLeft L e'.inv ≫ Functor.whiskerLeft L (Functor.whiskerLeft F' γ)
    let δ : H'.rightDerivedFunctorPlus ⟶ F'.rightDerivedFunctorPlus ⋙
        S.mapDerivedCategoryPlus :=
      (Functor.rightDerivedFunctorPlusCompIso' F' T e').inv ≫
        Functor.whiskerLeft F'.rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusNatTrans γ ≫
            S.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom)
    H.rightDerivedFunctorPlusUnith.app M ≫
        (H.rightDerivedFunctorPlus.map
          (adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M)) ≫
          (Functor.rightDerivedFunctorPlusCompIso' R H e).hom.app
            (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M))) ≫
        δ.app (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus b).app M) ≫
        S.mapDerivedCategoryPlusFactorsh.inv.app
          (F'.mapHomotopyCategoryPlus.obj (L.mapHomotopyCategoryPlus.obj M)) ≫
        S.mapDerivedCategoryPlus.map
          (F'.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj M)) ≫
        S.mapDerivedCategoryPlus.map
          (F'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app M)) := by
  dsimp only
  let δ : H'.rightDerivedFunctorPlus ⟶ F'.rightDerivedFunctorPlus ⋙
      S.mapDerivedCategoryPlus :=
    (Functor.rightDerivedFunctorPlusCompIso' F' T e').inv ≫
      Functor.whiskerLeft F'.rightDerivedFunctorPlus
        (Functor.rightDerivedFunctorPlusNatTrans γ ≫
          S.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom)
  -- Expand the derived adjunction unit and move its localization factor through Leray.
  have hu : adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app M) ≫
        R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj M) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app M) := by
    rw [← Category.assoc, ← adj.derivedPlus_unit_app_fac, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [hu, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (Functor.rightDerivedFunctorPlusCompIso' R H e).hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  have hH := H.rightDerivedFunctorPlusUnith.naturality
    (adj.mapHomotopyCategoryPlus.unit.app M)
  simp only [Functor.comp_map] at hH
  rw [← reassoc_of% hH]
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app_assoc]
  have hc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac R H e)
    (L.mapHomotopyCategoryPlus.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [reassoc_of% hc]
  have hg := δ.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hg
  erw [hg]
  let N := L.mapHomotopyCategoryPlus.obj M
  -- The inverse target Leray map carries the global-sections unit to the composite unit.
  have hf := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac F' T e') N
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hf
  have hf' : H'.rightDerivedFunctorPlusUnith.app N ≫
      (Functor.rightDerivedFunctorPlusCompIso' F' T e').inv.app
        (DerivedCategory.Plus.Qh.obj N) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e'.inv).app N) ≫
        (Functor.rightDerivedFunctorPlusCompUnit F' T).app N := by
    rw [← cancel_mono ((Functor.rightDerivedFunctorPlusCompIso' F' T e').hom.app
      (DerivedCategory.Plus.Qh.obj N))]
    rw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [Category.assoc, hf]
    rw [← Functor.map_comp_assoc, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id]
    simp
  dsimp only [δ]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [reassoc_of% hf']
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  -- Move the direct-image unit through the germ, then use exactness of the stalk.
  let τ := Functor.rightDerivedFunctorPlusNatTrans γ ≫
    S.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
  have ht := τ.naturality (F'.rightDerivedFunctorPlusUnith.app N)
  dsimp only [Functor.comp_obj] at ht
  dsimp only [τ, NatTrans.comp_app] at ht
  erw [reassoc_of% ht]
  have hs := NatTrans.congr_app S.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    (F'.mapHomotopyCategoryPlus.obj N)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hs
  rw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  erw [reassoc_of% hs]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 1
  apply DerivedCategory.Plus.Qh.congr_map
  -- The remaining identity is degreewise, checked through the faithful inclusion.
  apply (HomotopyCategory.Plus.ι A).map_injective
  obtain ⟨M, hM⟩ := M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  simp only [Category.assoc]
  change (H.mapHomotopyCategory _).map
      ((HomotopyCategory.Plus.ι C).map
        (adj.mapHomotopyCategoryPlus.unit.app ⟨_, hM⟩)) ≫ _ = _
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map]
  change (HomotopyCategory.quotient A _).map
      ((H.mapHomologicalComplex _).map ((adj.mapHomologicalComplex _).unit.app K)) ≫
    (HomotopyCategory.quotient A _).map
      ((NatTrans.mapHomologicalComplex e.hom _).app ((L.mapHomologicalComplex _).obj K)) ≫
    (HomotopyCategory.quotient A _).map
      ((NatTrans.mapHomologicalComplex e'.inv _).app ((L.mapHomologicalComplex _).obj K)) ≫
    (HomotopyCategory.quotient A _).map
      ((NatTrans.mapHomologicalComplex γ _).app
        ((F'.mapHomologicalComplex _).obj ((L.mapHomologicalComplex _).obj K))) =
    (HomotopyCategory.quotient A _).map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply (HomotopyCategory.quotient A _).congr_map
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change H.map (adj.unit.app (K.X n)) ≫ e.hom.app (L.obj (K.X n)) ≫
      e'.inv.app (L.obj (K.X n)) ≫ γ.app (F'.obj (L.obj (K.X n))) =
    𝟙 _ ≫ H.map (adj.unit.app (K.X n)) ≫ 𝟙 _ ≫ e.hom.app (L.obj (K.X n)) ≫
      e'.inv.app (L.obj (K.X n)) ≫ γ.app (F'.obj (L.obj (K.X n)))
  simp only [Category.id_comp]

-- The original interface retains the square and its unused source-side functors.
set_option linter.unusedVariables false in
/-- The target-side derived unit and germ, precomposed with the global-sections unit,
are the localized section-unit-and-germ composite followed by the target units.
Source: Stacks Project, cohomology.tex, Tags 01EZ and 01F8;
sites-cohomology.tex, Remark 08J6.
(blueprint: lem-weil-pbc-derived-global-germ-unit-fac)

Proof: Use `derivedCohomologyPullback_eq_derivedUnit` to replace Γ of the derived
adjunction unit followed by Leray by the derived pullback of sections. Its defining
right-derived descent formula, precomposed with Γ_X's unit, is the localized section
unit, followed by Γ_X' on the homotopy category and the inverse g'^* factorization.
Move that inverse across the target germ by naturality. Expand the target derived
germ: the Leray unit compatibility and the right-derived natural-transformation unit
compatibility turn Γ_X' followed by its germ into the localized inverse terminal
section identification and underived germ. The exact stalk comparison contributes the
inverse stalk factorization followed by the stalk image of the f'_* unit.
Combine localized maps using functoriality; the underived map is precisely b and the
remaining three comparisons, in their order, are c. -/
theorem derivedGlobalGerm_unit_fac
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (sq : CommSq g' f' f g)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y')
    (M : HomotopyCategory.Plus
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    let B := AddCommGrpCat.{u + 1}
    let F := lowerStar B f
    let F' := lowerStar B f'
    let G := upperStar B g
    let G' := upperStar B g'
    let R := lowerStar B g'
    let H := Sheaf.Γ X.smallEtaleTopology B
    let S := (pointSmallEtale t).sheafFiber
    let b : H ⟶ G' ⋙ F' ⋙ S :=
      (Functor.leftUnitor H).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction B g').unit H ≫
        (Functor.associator G' R H).hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B g').hom ≫
        Functor.whiskerLeft G' (lowerStarCompGlobalSectionsIso B f').inv ≫
        Functor.whiskerLeft G' (Functor.whiskerLeft F' (globalGerm t))
    let c := S.mapDerivedCategoryPlusFactorsh.inv.app
        (F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map
        (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj M)) ≫
      S.mapDerivedCategoryPlus.map (F'.rightDerivedFunctorPlus.map
        (G'.mapDerivedCategoryPlusFactorsh.inv.app M))
    H.rightDerivedFunctorPlusUnith.app M ≫
        (H.rightDerivedFunctorPlus.map
          ((upperStarLowerStarAdjunction B g').derivedPlus.unit.app
            (DerivedCategory.Plus.Qh.obj M)) ≫
          (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
            R H _ _ _ _
            (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
              (upperStarLowerStarAdjunction B g'))
            (lowerStarCompGlobalSectionsIso B g')).hom.app
              (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M))) ≫
        (derivedGlobalGerm f' t).app
          (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M)) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus b).app M) ≫ c := by
  dsimp only
  let B := AddCommGrpCat.{u + 1}
  let R := lowerStar B g'
  let F' := lowerStar B f'
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction B g')
  let : F'.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction B f')
  exact derived_unit_germ_fac (upperStar B g') R
    (Sheaf.Γ X.smallEtaleTopology B) (Sheaf.Γ X'.smallEtaleTopology B)
    F' (Sheaf.Γ Y'.smallEtaleTopology B) (pointSmallEtale t).sheafFiber
    (upperStarLowerStarAdjunction B g') (lowerStarCompGlobalSectionsIso B g')
    (lowerStarCompGlobalSectionsIso B f') (globalGerm t) M

end AlgebraicGeometry.Etale
