/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationSheafRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Homotopy normalization of a cartesian refinement

Source: Stacks Project, Tags 0F7I and 0D6E.
(blueprint: lem-sfb-compactification-refinement-homotopy-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private lemma open_unit_formula
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (O : C ⥤ D) (T : C ⥤ E) (L : E ⥤ D) (R : D ⥤ E)
    [O.Additive] [T.Additive] [L.Additive] [R.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (e : O ≅ T ⋙ L) (K : HomotopyCategory C (.up ℤ)) :
    T.mapDerivedCategoryFactorsh.inv.app K ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (T.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
        R.rightDerivedFunctor.map
          ((Functor.mapDerivedCategoryTriangleIso e).inv.app (DerivedCategory.Qh.obj K)) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((adj.mapHomotopyCategory (.up ℤ)).unit.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
          (R.mapHomotopyCategory (.up ℤ)).map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).hom.app K ≫
              (e.inv.mapHomotopyCategory (.up ℤ)).app K)) ≫
        R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) := by
  let bc := Functor.mapDerivedCategoryTriangleIso e
  let v := (Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).hom.app K ≫
    (e.inv.mapHomotopyCategory (.up ℤ)).app K
  let w := (e.hom.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).inv.app K
  have ht : bc.hom.app (DerivedCategory.Qh.obj K) ≫
      L.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app K) ≫
      L.mapDerivedCategoryFactorsh.hom.app ((T.mapHomotopyCategory (.up ℤ)).obj K) =
      O.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map w := by
    have h := Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj e K
    have hh := congrArg (fun t ↦ O.mapDerivedCategoryFactorsh.hom.app K ≫ t) h
    simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using hh
  have he : w ≫ v = 𝟙 _ := by
    dsimp only [w, v]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
    rfl
  have hb : L.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.inv.app K) ≫
      bc.inv.app (DerivedCategory.Qh.obj K) ≫ O.mapDerivedCategoryFactorsh.hom.app K =
      L.mapDerivedCategoryFactorsh.hom.app ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map v := by
    apply (cancel_epi (bc.hom.app (DerivedCategory.Qh.obj K) ≫
      L.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app K))).1
    simp only [Category.assoc]
    rw [← L.mapDerivedCategory.map_comp_assoc, Iso.hom_inv_id_app]
    erw [L.mapDerivedCategory.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% ht, ← DerivedCategory.Qh.map_comp, he,
      DerivedCategory.Qh.map_id, Category.comp_id]
  have hu : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (DerivedCategory.Qh.obj ((T.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      R.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactorsh.hom.app ((T.mapHomotopyCategory (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
        ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((T.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      R.rightDerivedFunctorUnit.app
        ((L.mapHomotopyCategory (.up ℤ)).obj ((T.mapHomotopyCategory (.up ℤ)).obj K)) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso E (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit ((T.mapHomotopyCategory (.up ℤ)).obj K)
  change _ ≫ _ ≫ R.rightDerivedFunctor.map (bc.inv.app _) ≫ _ =
    DerivedCategory.Qh.map (_ ≫ (R.mapHomotopyCategory (.up ℤ)).map v) ≫ _
  rw [reassoc_of% (adj.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (T.mapDerivedCategoryFactorsh.inv.app K))]
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj]
  rw [← R.rightDerivedFunctor.map_comp, ← R.rightDerivedFunctor.map_comp, hb,
    R.rightDerivedFunctor.map_comp]
  rw [reassoc_of% hu]
  have hn := R.rightDerivedFunctorUnit.naturality v
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn, ← DerivedCategory.Qh.map_comp_assoc]

private lemma right_comp_unit_raw
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (R : C ⥤ D) (P : D ⥤ E) [R.Additive] [P.Additive]
    [R.PreservesKInjectiveComplexes] {S : C ⥤ E} [S.Additive]
    (e : R ⋙ P ≅ S) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit R P).app K ≫
        (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app K) ≫
        S.rightDerivedFunctorUnit.app K := by
  have h : (Functor.rightDerivedFunctorCompUnit R P).app K ≫
      (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      (R ⋙ P).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Qh.obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  rw [h]
  exact Functor.rightDerivedNatTrans_app (R ⋙ P).rightDerivedFunctor S.rightDerivedFunctor
    (R ⋙ P).rightDerivedFunctorUnit S.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (e.hom.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh) K

private lemma right_comp_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (R : C ⥤ D) (P : D ⥤ E) [R.Additive] [P.Additive]
    [R.PreservesKInjectiveComplexes] {S : C ⥤ E} [S.Additive]
    (e : R ⋙ P ≅ S) (K : HomotopyCategory C (.up ℤ)) :
    P.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        P.rightDerivedFunctor.map (R.rightDerivedFunctorUnit.app K) ≫
        (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).hom.app K ≫
          (e.hom.mapHomotopyCategory (.up ℤ)).app K) ≫
        S.rightDerivedFunctorUnit.app K := by
  have h := right_comp_unit_raw R P e K
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] at h
  apply (cancel_epi (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).inv.app K))).1
  simp only [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact h

private lemma refinement_unit
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory V]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
    (O : C ⥤ D) (T : C ⥤ E) (L : E ⥤ D) (R : D ⥤ E) (P : E ⥤ V) (S : D ⥤ V)
    [O.Additive] [T.Additive] [L.Additive] [R.Additive] [P.Additive] [S.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.PreservesKInjectiveComplexes]
    (adj : L ⊣ R) (e : O ≅ T ⋙ L) (i : R ⋙ P ≅ S)
    (F : C ⥤ V) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⟶ T ⋙ P) (t : T ⋙ P ⟶ O ⋙ S)
    (htdef : t =
      Functor.whiskerRight
          (Functor.whiskerLeft T adj.unit ≫ Functor.whiskerRight e.inv R) P ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft O i.hom) :
    normalizationHomotopyTransformation F T P a ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.whiskerRight
            (Functor.whiskerLeft T.mapDerivedCategory
              adj.mapDerivedCategoryRightDerivedAdjunction.unit) P.rightDerivedFunctor ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso e).inv
            (R.rightDerivedFunctor ⋙ P.rightDerivedFunctor) ≫
          Functor.whiskerLeft O.mapDerivedCategory
            (Functor.rightDerivedFunctorCompIso' R P i).hom) =
      normalizationHomotopyTransformation F O S (a ≫ t) := by
  let bc := Functor.mapDerivedCategoryTriangleIso e
  let comp := Functor.rightDerivedFunctorCompIso' R P i
  ext K
  let α := (adj.mapHomotopyCategory (.up ℤ)).unit.app
      ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (R.mapHomotopyCategory (.up ℤ)).map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).hom.app K ≫
        (e.inv.mapHomotopyCategory (.up ℤ)).app K)
  let κ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).hom.app
      ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (i.hom.mapHomotopyCategory (.up ℤ)).app
      ((O.mapHomotopyCategory (.up ℤ)).obj K)
  have hγ := open_unit_formula O T L R adj e K
  have ht : ((a ≫ t).mapHomotopyCategory
      (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ S)) (.up ℤ)).inv.app K =
      (a.mapHomotopyCategory (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ P)) (.up ℤ)).inv.app K ≫
        (P.mapHomotopyCategory (.up ℤ)).map α ≫ κ := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    dsimp only [α, κ]
    have hu : (adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((T.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
        (HomotopyCategory.quotient _ (.up ℤ)).map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app
            ((T.mapHomologicalComplex (.up ℤ)).obj J)) :=
      Adjunction.mapHomotopyCategory_unit_app_quotient _ adj _
    rw [hu]
    have hz : ((a ≫ t).mapHomologicalComplex
        (.up ℤ)).app J ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (O ⋙ S)) (.up ℤ)).inv.app J =
        (a.mapHomologicalComplex (.up ℤ)).app J ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ P)) (.up ℤ)).inv.app J ≫
          (P.mapHomologicalComplex (.up ℤ)).map
            ((adj.mapHomologicalComplex (.up ℤ)).unit.app
                ((T.mapHomologicalComplex (.up ℤ)).obj J) ≫
              (R.mapHomologicalComplex (.up ℤ)).map
                ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ L))
                    (.up ℤ)).hom.app J ≫
                  (e.inv.mapHomologicalComplex (.up ℤ)).app J)) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).hom.app
            ((O.mapHomologicalComplex (.up ℤ)).obj J) ≫
          (i.hom.mapHomologicalComplex (.up ℤ)).app
            ((O.mapHomologicalComplex (.up ℤ)).obj J) := by
      ext1 n
      simp only [htdef, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
        Functor.mapHomologicalComplexCompIso_hom_app_f,
        Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
        NatTrans.id_app, Category.id_comp, Functor.comp_obj,
        Functor.map_comp, Category.assoc]
      erw [Category.comp_id, Category.id_comp, R.map_id, P.map_id,
        Category.id_comp, Category.id_comp]
      rfl
    have hh := (HomotopyCategory.quotient _ (.up ℤ)).congr_map hz
    simp only [Functor.map_comp] at hh ⊢
    exact hh
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app,
    Category.assoc] at ht
  have hc := right_comp_unit R P i
    ((O.mapHomotopyCategory (.up ℤ)).obj K)
  apply (cancel_mono (S.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K))).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    normalizationHomotopyTransformation_app, normalizationHomotopyComponent,
    Functor.whiskerRight_app, Functor.comp_map,
    NatTrans.mapHomotopyCategory_comp, Category.assoc]
  have hn := comp.hom.naturality (O.mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  slice_lhs 5 8 =>
    rw [← P.rightDerivedFunctor.map_comp, ← P.rightDerivedFunctor.map_comp,
      ← P.rightDerivedFunctor.map_comp]
    erw [hγ, P.rightDerivedFunctor.map_comp]
  have hp := P.rightDerivedFunctorUnit.naturality α
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hp
  simp only [Category.assoc]
  erw [← reassoc_of% hp]
  rw [hc]
  rw [← S.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [S.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  simpa only [κ, Category.assoc] using congrArg
    (fun t ↦ F.mapDerivedCategoryFactorsh.hom.app K ≫ DerivedCategory.Qh.map t ≫
      S.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K)) ht.symm

/-- Pasting the exact-source unit with a single cartesian derived refinement is the
homotopy unit of the explicitly transported sheaf map. The input map need not be invertible.
Source: Stacks Project, Tags 0F7I and 0D6E.
(blueprint: lem-sfb-compactification-refinement-homotopy-unit).

Proof: expand the derived refinement into the unit of inverse image/direct image,
inverse open base change and the derived direct-image composition isomorphism. On a
homotopy representative, the derived adjunction unit is the ordinary adjunction unit
followed by the right-derived unit, with the exact inverse-image factorization removed.
Naturality moves inverse open base change through that unit. The composition-unit identity
then combines the units for the refinement pushforward and the coarser proper pushforward
into the unit for the finer proper pushforward. Naturality moves the input sheaf map through
these identities. The remaining ordinary factors are exactly
compactificationSheafRefinement, and the exact factors are exactly those of
normalizationHomotopyTransformation. This proves equality before localization, for every
homotopy complex; no support-inclusion cancellation or common refinement is used. -/
theorem compactificationRefinement_homotopyUnit
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g) :
    normalizationHomotopyTransformation F
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i)
        (lowerStar (ModuleCat.{u + 1} A) d.g) a ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hcart) =
    normalizationHomotopyTransformation F
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g)
      (a ≫ compactificationSheafRefinement A r hcart) := by
  let B := ModuleCat.{u + 1} A
  have := r.isIso_openImmersionLowerShriekBaseChange B hcart
  exact refinement_unit
    (openImmersionLowerShriek B c.i) (openImmersionLowerShriek B d.i)
    (upperStar B r.hom) (lowerStar B r.hom) (lowerStar B d.g) (lowerStar B c.g)
    (upperStarLowerStarAdjunction B r.hom)
    (asIso (r.openImmersionLowerShriekBaseChange B)) (refinementLowerStarComp B r)
    F a (compactificationSheafRefinement A r hcart) (by rfl)

end AlgebraicGeometry.Etale
