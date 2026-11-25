/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Degree-zero restriction and coefficient transport

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-derived-restriction-zero-transport).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison


set_option backward.isDefEq.respectTransparency false in
/-- Exact derived composition agrees with the two single comparisons.
Source: Mathlib `mapDerivedCategoryCompIso_fac` and naturality of
`mapDerivedCategoryFactors`; the final complex equality is checked in degree zero.
(blueprint: lem-sbc-derived-restriction-zero-transport). -/
private theorem single_comp {C D E : Type*} [Category C] [Category D] [Category E]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [CategoryTheory.Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (X : C) :
    (Functor.mapDerivedCategoryCompIso F H).inv.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      H.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
    ((F ⋙ H).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso F H).hom.app _),
    Iso.hom_inv_id_app_assoc]
  exact (F.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app
    H X 0).symm

/-- A derived natural isomorphism agrees with its coefficient map on a single object.
Source: `mapDerivedCategoryNatIso_fac` and the definition of
`mapDerivedCategorySingleFunctor`; check the resulting complex map in degree zero.
(blueprint: lem-sbc-derived-restriction-zero-transport). -/
private theorem single_nat {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (F H : C ⥤ D) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ≅ H) (X : C) :
    (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app X =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  dsimp [DerivedCategory.singleFunctorIsoCompQ]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp, Category.assoc]
  erw [Functor.mapDerivedCategoryNatIso_fac_assoc]
  change F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
          ((CochainComplex.singleFunctor C 0).obj X)) ≫
      DerivedCategory.Q.map ((H.mapCochainComplexSingleFunctor 0).hom.app X) =
    F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map (e.hom.app X))
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply HomologicalComplex.to_single_hom_ext
  simp only [Functor.comp_obj, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f]
  change e.hom.app X ≫
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app X).f 0 =
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X).f 0 ≫
      ((HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X)).f 0
  simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]

/-- Combine the composition and natural-isomorphism calculations for an exact square.
Source: Stacks Project, Tag 0D6F, functoriality of localization.
(blueprint: lem-sbc-derived-restriction-zero-transport). -/
private theorem single_square {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [CategoryTheory.Abelian D']
    [CategoryTheory.Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory D'] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ D') (H' : D' ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive] [H'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    (e : F ⋙ H ≅ F' ⋙ H') (X : C) :
    (Functor.mapDerivedCategoryCompIso F H ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso F' H').symm).hom.app
          ((DerivedCategory.singleFunctor C 0).obj X) ≫
      H'.mapDerivedCategory.map ((F'.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (H'.mapDerivedCategorySingleFunctor 0).hom.app (F'.obj X) =
    H.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [single_comp, single_nat, ← single_comp F H]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The single-object degree-zero right-derived comparison is natural.
Source: naturality of `rightDerivedFunctorPlusCompatibility`,
`homologyRightDerivedFunctorPlusObjSingleFunctorIso`, and `rightDerivedZeroIsoSelf`.
(blueprint: lem-sbc-derived-restriction-zero-transport). -/
private theorem zero_single_naturality {C D : Type*} [Category C] [Category D]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D]
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] {X Y : C} (f : X ⟶ Y) :
    (DerivedCategory.homologyFunctor D 0).map
        (R.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map f)) ≫
      (R.homologyRightDerivedFunctorObjSingleFunctorIso Y 0 ≪≫
        R.rightDerivedZeroIsoSelf.app Y).hom =
    (R.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫
        R.rightDerivedZeroIsoSelf.app X).hom ≫ R.map f := by
  dsimp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc]
  have hn := R.rightDerivedFunctorPlusCompatibility.inv.naturality
    ((DerivedCategory.Plus.singleFunctor C 0).map f)
  change R.rightDerivedFunctor.map ((DerivedCategory.singleFunctor C 0).map f) ≫
      (R.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y)).inv =
    (R.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X)).inv ≫
      DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor C 0).map f)) at hn
  rw [hn]
  simp only [Functor.map_comp, Category.assoc]
  erw [R.homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality_assoc]
  erw [R.rightDerivedZeroIsoSelf.hom.naturality]
  rfl

/-- Degree-zero coefficient transport for an arbitrary square of exact functors.
Source: Stacks Project, Tag 0D6F, restriction, and functoriality of localization.
First apply the single-square calculation and naturality of the target single comparison.
Then apply derived sections and zeroth homology. Finally use the naturality of the
single-object degree-zero right-derived comparison. No coefficient isomorphism is assumed.
(blueprint: lem-sbc-derived-restriction-zero-transport). -/
private theorem square_zero_transport {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E]
    [CategoryTheory.Abelian C] [CategoryTheory.Abelian D] [CategoryTheory.Abelian D']
    [CategoryTheory.Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory D'] [HasDerivedCategory E]
    [EnoughInjectives E] [CategoryTheory.Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (Q : D ⥤ E) (A : C ⥤ D') (L' : D' ⥤ E)
    [L.Additive] [Q.Additive] [A.Additive] [L'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (R : E ⥤ AddCommGrpCat.{v + 1}) [R.Additive] [PreservesFiniteLimits R]
    (t : L ⋙ Q ≅ A ⋙ L') (X : C) (Y : D') (f : A.obj X ⟶ Y) :
    (let e := Functor.mapDerivedCategoryCompIso L Q ≪≫
        Functor.mapDerivedCategoryNatIso t ≪≫ (Functor.mapDerivedCategoryCompIso A L').symm
    let b := L.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app X) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app X
    let c := Q.mapDerivedCategory.map b.hom ≫
      (Q.mapDerivedCategorySingleFunctor 0).hom.app (L.obj X)
    let z := R.homologyRightDerivedFunctorObjSingleFunctorIso (Q.obj (L.obj X)) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (Q.obj (L.obj X))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map (e.hom.app
          (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj X)))) ≫
      (Evaluation.functor L' R ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map f) ≫ (Evaluation.zeroIso L' R Y).hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map c) ≫ z.hom ≫ R.map (t.hom.app X ≫ L'.map f)) := by
  intro e b c z
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  let T := R.rightDerivedFunctor ⋙ H
  have ht := single_square L Q A L' t X
  have hz := zero_single_naturality R (t.hom.app X ≫ L'.map f)
  have hb : b.hom = (L.mapDerivedCategorySingleFunctor 0).hom.app X := by
    dsimp only [b, Iso.trans_hom, Functor.mapIso_hom,
      DerivedCategory.Plus.singleFunctorιIso]
    simp only [Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hc : e.hom.app ((DerivedCategory.singleFunctor _ 0).obj X) ≫
      L'.mapDerivedCategory.map ((A.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor _ 0).map f) ≫
      (L'.mapDerivedCategorySingleFunctor 0).hom.app Y =
    c ≫ (DerivedCategory.singleFunctor _ 0).map (t.hom.app X ≫ L'.map f) := by
    dsimp only [c]
    rw [hb]
    simp only [Functor.map_comp, Category.assoc]
    erw [(L'.mapDerivedCategorySingleFunctor 0).hom.naturality f]
    simp only [Functor.comp_map]
    erw [reassoc_of% ht]
  have hm := congrArg T.map hc
  simp only [Functor.map_comp, Category.assoc] at hm
  dsimp only [T, Functor.comp_map, H] at hm
  simp only [Evaluation.zeroIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, DerivedCategory.Plus.singleFunctorιIso, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id]
  simp only [CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [A.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  erw [reassoc_of% hm]
  simp only [Functor.map_comp, Iso.trans_hom, Category.assoc] at hz
  erw [hz]
  simp only [z, Iso.trans_hom, Category.assoc]
  rfl

/-- The restriction triangle and a coefficient morphism respect the zero comparison.
Source: Stacks Project, Tag 0D6F, restriction, and functoriality of localization.
(blueprint: lem-sbc-derived-restriction-zero-transport).

Proof: Expand the derived restriction isomorphism into its three factors.
The localization factorization of mapDerivedCategoryCompIso identifies each
composition factor on a single complex with its underived composition factor.
The factorization of mapDerivedCategoryNatIso identifies the middle factor with
the single of the upperStarComp comparison. The singleFunctorιIso and exact
single comparisons cancel between adjacent factors. After these cancellations
the resulting map of single complexes is the single of
rawAffineRestrictedCoefficient. Apply derived sections and zeroth homology.
Naturality of the right-derived single homology comparison, followed by
naturality of rightDerivedZeroIsoSelf, gives the section map of that coefficient
morphism. The remaining outer single comparisons are exactly those displayed
in zeroIso. This uses no invertibility of the coefficient map and also applies
to the empty scheme. -/
theorem derivedRestriction_zero_transport {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ψ : (upperStar AddCommGrpCat.{v + 1} a).obj G ⟶ G') (U : S.Etale) :
    (let e : D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)) ≅
      D(upperStar AddCommGrpCat.{v + 1} a) ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')) := by
      let q := rawAffineRestrictedMap a h h' w U
      let r := Limits.pullback.snd U.hom h
      let r' := Limits.pullback.snd U.hom h'
      have hw : r' ≫ a = q ≫ r := by simp [q, r, r', rawAffineRestrictedMap]
      exact (Functor.mapDerivedCategoryCompIso _ _) ≪≫
        Functor.mapDerivedCategoryNatIso ((upperStarComp AddCommGrpCat.{v + 1} q r).symm ≪≫
          upperStarComp AddCommGrpCat.{v + 1} r' a (q ≫ r) hw.symm) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm
    let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
    let W' := (MorphismProperty.Over.pullback @Etale ⊤ h').obj U
    let L := upperStar AddCommGrpCat.{v + 1} W.hom
    let Q := upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
    let R := Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}
    let b := L.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app G
    let c := Q.mapDerivedCategory.map b.hom ≫
      (Q.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
    let z := R.homologyRightDerivedFunctorObjSingleFunctorIso (Q.obj (L.obj G)) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (Q.obj (L.obj G))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map (e.hom.app
          (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
      (sectionsFunctor W' ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map ψ) ≫ (zeroIso W' G').hom =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map c) ≫ z.hom ≫
          R.map (rawAffineRestrictedCoefficient a h h' w G G' ψ U)) := by
  intro e W W' L Q R b c z
  let A := upperStar AddCommGrpCat.{v + 1} a
  let L' := upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')
  let q := rawAffineRestrictedMap a h h' w U
  let r := Limits.pullback.snd U.hom h
  let r' := Limits.pullback.snd U.hom h'
  have hw : r' ≫ a = q ≫ r := by simp [q, r, r', rawAffineRestrictedMap]
  let t : L ⋙ Q ≅ A ⋙ L' :=
    (upperStarComp AddCommGrpCat.{v + 1} q r).symm ≪≫
      upperStarComp AddCommGrpCat.{v + 1} r' a (q ≫ r) hw.symm
  exact square_zero_transport
    (upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)) Q A L' R t G G' ψ

end AlgebraicGeometry.Etale.RawRestrictedComparison
