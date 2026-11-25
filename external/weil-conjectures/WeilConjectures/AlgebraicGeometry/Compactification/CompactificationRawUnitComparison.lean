/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import all WeilConjectures.AlgebraicGeometry.Compactification.CompactificationRefinementHomotopyUnit

/-! # Common refinements preserve the raw homotopy unit -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private lemma raw_refinement_unit
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
    (t : T ⋙ P ⟶ O ⋙ S)
    (htdef : t =
      Functor.whiskerRight
          (Functor.whiskerLeft T adj.unit ≫ Functor.whiskerRight e.inv R) P ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft O i.hom)
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T P).app K ≫
        (Functor.whiskerRight
            (Functor.whiskerLeft T.mapDerivedCategory
              adj.mapDerivedCategoryRightDerivedAdjunction.unit) P.rightDerivedFunctor ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso e).inv
            (R.rightDerivedFunctor ⋙ P.rightDerivedFunctor) ≫
          Functor.whiskerLeft O.mapDerivedCategory
            (Functor.rightDerivedFunctorCompIso' R P i).hom).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((t.mapHomotopyCategory (.up ℤ)).app K) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O S).app K := by
  let bc := Functor.mapDerivedCategoryTriangleIso e
  let comp := Functor.rightDerivedFunctorCompIso' R P i
  let α := (adj.mapHomotopyCategory (.up ℤ)).unit.app
      ((T.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (R.mapHomotopyCategory (.up ℤ)).map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ L)) (.up ℤ)).hom.app K ≫
        (e.inv.mapHomotopyCategory (.up ℤ)).app K)
  let κ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).hom.app
      ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (i.hom.mapHomotopyCategory (.up ℤ)).app ((O.mapHomotopyCategory (.up ℤ)).obj K)
  have hγ := open_unit_formula O T L R adj e K
  have ht : (t.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ S)) (.up ℤ)).inv.app K =
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
      Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) adj _
    rw [hu]
    have hz : (t.mapHomologicalComplex (.up ℤ)).app J ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (O ⋙ S)) (.up ℤ)).inv.app J =
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
  have hc := right_comp_unit R P i ((O.mapHomotopyCategory (.up ℤ)).obj K)
  apply (cancel_mono (S.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K))).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    Functor.whiskerRight_app, Functor.comp_map, Category.assoc]
  have hn := comp.hom.naturality (O.mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  slice_lhs 3 6 =>
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
    (fun t ↦ DerivedCategory.Qh.map t ≫
      S.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K)) ht.symm

private lemma raw_refinement
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i)
        (lowerStar (ModuleCat.{u + 1} A) d.g)).app K ≫
      (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) r hcart).app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map
        (((compactificationSheafRefinement A r hcart).mapHomotopyCategory (.up ℤ)).app K) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStar (ModuleCat.{u + 1} A) c.g)).app K := by
  let B := ModuleCat.{u + 1} A
  have := r.isIso_openImmersionLowerShriekBaseChange B hcart
  exact raw_refinement_unit
    (openImmersionLowerShriek B c.i) (openImmersionLowerShriek B d.i)
    (upperStar B r.hom) (lowerStar B r.hom) (lowerStar B d.g) (lowerStar B c.g)
    (upperStarLowerStarAdjunction B r.hom)
    (asIso (r.openImmersionLowerShriekBaseChange B)) (refinementLowerStarComp B r)
    (compactificationSheafRefinement A r hcart) rfl K

/-- Common-refinement comparison preserves a sheaf map followed by the mixed derived unit.
The input sheaf functor is only additive; its exactness is unnecessary because its derived
functor does not occur.

Source: Stacks Project, Tags 0F7B, 0F7I and 0D6E.
(blueprint: lem-pur-compactification-raw-unit-comparison).

Proof in words: first take a Cartesian proper refinement. Expand its comparison as the
adjunct of inverse open base change followed by proper direct-image composition. The
mixed adjunction unit equation identifies its composite with the open/proper derived
unit with the homotopy image of the ordinary sheaf refinement followed by the finer unit.
Direct-image composition preserves the units because proper direct image preserves
K-injectives. Naturality permits precomposition with any additive sheaf map. For c and d,
pass to their canonical common refinement. The two sheaf maps into this refinement agree:
their composites with its monic inclusion in ordinary direct image agree by the hypothesis.
Apply the refinement identity twice and cancel the invertible finer comparison. The result
is exactly the common-refinement isomorphism used in the statement. Identity refinements,
zero input maps and empty schemes require no separate assumption. -/
theorem compactification_raw_unit_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) [F.Additive]
    (c d : Compactification f)
    (a : F ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g)
    (b : F ⟶ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (hab : a ≫ compactificationSheafToDirectImage A c =
      b ≫ compactificationSheafToDirectImage A d)
    (J : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app J ≫
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
          (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((b.mapHomotopyCategory (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i)
          (lowerStar (ModuleCat.{u + 1} A) d.g)).app J := by
  let e := Compactification.inf c d
  let r := Compactification.infFst c d
  let s := Compactification.infSnd c d
  have hr := Compactification.isPullback_infFst c d
  have hs := Compactification.isPullback_infSnd c d
  obtain ⟨hn, hm⟩ := compactificationSheafRefinement_properties A r hr
  have he : a ≫ compactificationSheafRefinement A r hr =
      b ≫ compactificationSheafRefinement A s hs := by
    have : ∀ M, Mono ((compactificationSheafToDirectImage A e).app M) := hm
    have : Mono (compactificationSheafToDirectImage A e) := NatTrans.mono_of_mono_app _
    apply (cancel_mono (compactificationSheafToDirectImage A e)).1
    rw [Category.assoc, Category.assoc, hn,
      (compactificationSheafRefinement_properties A s hs).1]
    exact hab
  have h₁ := raw_refinement A r hr J
  have h₂ := raw_refinement A s hs J
  have ht : DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app J) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStar (ModuleCat.{u + 1} A) c.g)).app J ≫
      (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) r hr).app (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map ((b.mapHomotopyCategory (.up ℤ)).app J) ≫
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i)
        (lowerStar (ModuleCat.{u + 1} A) d.g)).app J ≫
      (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) s hs).app (DerivedCategory.Qh.obj J) := by
    rw [h₁, h₂, ← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc]
    simp only [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, he]
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, asIso_hom]
  rw [reassoc_of% ht]
  have hc := congr_app (asIso (rightDerivedLowerShriekOfCompactificationComparison
    (ModuleCat.{u + 1} A) s hs)).hom_inv_id (DerivedCategory.Qh.obj J)
  simp only [NatTrans.comp_app, NatTrans.id_app, asIso_hom] at hc
  rw [hc]
  erw [Category.comp_id]

end AlgebraicGeometry.Etale
