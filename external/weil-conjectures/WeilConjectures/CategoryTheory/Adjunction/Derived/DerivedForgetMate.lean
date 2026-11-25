/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-!
# Deriving an adjoint square with exact vertical functors

Source: blueprint thm-weil-pbc-qbar.proof.md, "Forgetting the Weil structure";
Stacks Project, Derived Categories, Tags 09T5, 0DVC and 0FND.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} {C₀ : Type u₃} {D₀ : Type u₄}
  [Category.{v} C] [Category.{v} D] [Category.{v} C₀] [Category.{v} D₀]
  [Abelian C] [Abelian D] [Abelian C₀] [Abelian D₀]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory C₀] [HasDerivedCategory D₀]
  [HasKInjectiveResolutions D] [HasKInjectiveResolutions C]
  [HasKInjectiveResolutions D₀]
  {L : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}
  [L.Additive] [R.Additive] [L₀.Additive] [R₀.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
  (adj : L ⊣ R) (adj₀ : L₀ ⊣ R₀)
  (U : C ⥤ C₀) (V : D ⥤ D₀) [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [V.PreservesKInjectiveComplexes]

private lemma homotopy_comp_inv_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X = 𝟙 _ := by
  have h := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).hom_inv_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

-- Preserve the original resolution hypothesis, although this calculation does not need it.
set_option linter.unusedSectionVars false in
/-- The canonical right-derived comparison is the mate of the localized left comparison.
Source: blueprint thm-weil-pbc-qbar.proof.md, "Forgetting the Weil structure";
Stacks Project, Derived Categories, Tags 09T5, 0DVC and 0FND.
(blueprint: lem-sf-derived-exact-forget-mate).

Proof: lift the compatible abelian adjunction square to cochain complexes and then to
homotopy categories. Both `RR ⋙ D(U)` and `D(V) ⋙ RR₀` are right derived functors of the
same homotopy functor: exactness of U gives the first assertion and preservation of
K-injectives by V gives the second. Uniqueness of right derived functors identifies their
comparison with the displayed composition of the four canonical comparison isomorphisms.
Its defining equation on localized complexes is the right-derived unit equation. The
canonical derived adjunction has the localized Hom formula (equivalently its unit and
counit satisfy `derivedη_fac_app` and `derivedε_fac_app`). Apply the compatible derived
adjoint-square comparison to the underived mate equality, the localized left comparison,
and this normalized right comparison. It gives the derived unit equation. The mate is
uniquely determined by that unit equation, by adjunction transposition, proving the claim.
No invertibility of a general mate is inferred: invertibility here comes from the two
right-derived universal properties. -/
theorem derived_exact_forget_mate (a : L ⋙ V ≅ U ⋙ L₀) (b : R ⋙ U ≅ V ⋙ R₀)
    (hb : (mateEquiv adj adj₀ (TwoSquare.mk _ _ _ _ a.inv)) = b.hom) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj₀.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso a).inv)) =
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso R U).symm ≪≫
        Functor.rightDerivedFunctorNatIso b ≪≫
        Functor.rightDerivedFunctorCompIso V R₀ ≪≫
        Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory
          R₀.rightDerivedFunctor).hom := by
  let β := ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso R U).symm ≪≫
    Functor.rightDerivedFunctorNatIso b ≪≫
    Functor.rightDerivedFunctorCompIso V R₀ ≪≫
    Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory
      R₀.rightDerivedFunctor).hom
  let aD := Functor.mapDerivedCategorySquareIso a
  let d := adj.mapDerivedCategoryRightDerivedAdjunction
  let d₀ := adj₀.mapDerivedCategoryRightDerivedAdjunction
  -- The canonical comparisons are normalized by their right-derived units.
  have hcomp : Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R U ≫
      Functor.whiskerLeft DerivedCategory.Qh β =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory b.hom (.up ℤ)) DerivedCategory.Qh ≫
      Functor.rightDerivedFunctorCompUnit V R₀ ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory
          R₀.rightDerivedFunctor).hom := by
    ext X
    simp [β, Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedFunctorCompIso, Functor.rightDerivedFunctorNatIso,
      Functor.rightDerivedFunctorNatTrans]
  have hβ (X : HomotopyCategory D (.up ℤ)) :
      U.mapDerivedCategoryFactorsh.inv.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
        U.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
        β.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app X) ≫
        R₀.rightDerivedFunctorUnit.app ((V.mapHomotopyCategory (.up ℤ)).obj X) ≫
        R₀.rightDerivedFunctor.map (V.mapDerivedCategoryFactorsh.inv.app X) := by
    have h := congr_app hcomp X
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit,
      Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, homotopy_comp_inv_app,
      Category.id_comp, Category.assoc] at h
    have hf := congr_app V.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [← R₀.rightDerivedFunctor.map_comp, hf] at h
    erw [Functor.map_id, Category.id_comp, Functor.map_id, Category.id_comp] at h
    exact h
  -- Use the units of the specified canonical derived adjunctions.
  have hη (X : HomotopyCategory C (.up ℤ)) :
      d.unit.app (DerivedCategory.Qh.obj X) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app X) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj X) := by
    exact (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit X
  have hη₀ (X : HomotopyCategory C₀ (.up ℤ)) :
      d₀.unit.app (DerivedCategory.Qh.obj X) ≫
        R₀.rightDerivedFunctor.map (L₀.mapDerivedCategoryFactorsh.hom.app X) =
      DerivedCategory.Qh.map ((adj₀.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        R₀.rightDerivedFunctorUnit.app ((L₀.mapHomotopyCategory (.up ℤ)).obj X) := by
    exact (adj₀.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C₀ (.up ℤ))
      L₀.mapDerivedCategoryFactorsh.hom R₀.rightDerivedFunctorUnit X
  -- The ordinary mate identity lifts degreewise to homotopy complexes.
  have hc (X : HomotopyCategory C (.up ℤ)) :
      (U.mapHomotopyCategory (.up ℤ)).map
          ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        (NatTrans.mapHomotopyCategory b.hom (.up ℤ)).app
          ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      (adj₀.mapHomotopyCategory (.up ℤ)).unit.app
          ((U.mapHomotopyCategory (.up ℤ)).obj X) ≫
        (R₀.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory a.inv (.up ℤ)).app X) := by
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    erw [mapHomotopyCategory_unit_app_quotient,
      mapHomotopyCategory_unit_app_quotient]
    change (HomotopyCategory.quotient C₀ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₀ (.up ℤ)).map _ =
      (HomotopyCategory.quotient C₀ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₀ (.up ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    change U.map (adj.unit.app (M.X n)) ≫ b.hom.app (L.obj (M.X n)) =
      adj₀.unit.app (U.obj (M.X n)) ≫ R₀.map (a.inv.app (M.X n))
    rw [← hb]
    exact unit_mateEquiv adj adj₀ (TwoSquare.mk _ _ _ _ a.inv) (M.X n)
  -- Invert the localization formula for the left square, retaining every factor.
  have haDi (X : HomotopyCategory C (.up ℤ)) :
      L₀.mapDerivedCategory.map (U.mapDerivedCategoryFactorsh.hom.app X) ≫
        L₀.mapDerivedCategoryFactorsh.hom.app ((U.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a.inv (.up ℤ)).app X) ≫
        V.mapDerivedCategoryFactorsh.inv.app ((L.mapHomotopyCategory (.up ℤ)).obj X) ≫
        V.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app X) =
      aD.inv.app (DerivedCategory.Qh.obj X) := by
    have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj a X
    simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, homotopy_comp_inv_app,
      Category.id_comp, Category.comp_id] at h
    change V.mapDerivedCategoryFactorsh.inv.app
        ((L.mapHomotopyCategory (.up ℤ)).obj X) ≫
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app X) ≫
      aD.hom.app (DerivedCategory.Qh.obj X) ≫
      L₀.mapDerivedCategory.map (U.mapDerivedCategoryFactorsh.hom.app X) ≫
      L₀.mapDerivedCategoryFactorsh.hom.app ((U.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X) at h
    have hi : (NatTrans.mapHomotopyCategory a.hom (.up ℤ)).app X ≫
        (NatTrans.mapHomotopyCategory a.inv (.up ℤ)).app X = 𝟙 _ := by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, a.hom_inv_id]
      simp
    have h' := congrArg (fun f ↦ aD.inv.app (DerivedCategory.Qh.obj X) ≫
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      V.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) ≫
      f ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory a.inv (.up ℤ)).app X) ≫
      V.mapDerivedCategoryFactorsh.inv.app ((L.mapHomotopyCategory (.up ℤ)).obj X) ≫
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app X)) h
    simp only [Category.assoc, ← Functor.map_comp_assoc, hi,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc] at h'
    erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at h'
    erw [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc] at h'
    rw [← Functor.map_comp, Iso.hom_inv_id_app] at h'
    erw [Functor.map_id, Category.comp_id] at h'
    exact h'
  -- Paste the normalized comparison with the derived unit on each Qh(X).
  have hq (X : HomotopyCategory C (.up ℤ)) :
      U.mapDerivedCategory.map (d.unit.app (DerivedCategory.Qh.obj X)) ≫
        β.app (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      d₀.unit.app (U.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        R₀.rightDerivedFunctor.map (aD.inv.app (DerivedCategory.Qh.obj X)) := by
    have hη' : d.unit.app (DerivedCategory.Qh.obj X) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj X) ≫
          R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app X) := by
      rw [← Category.assoc, ← hη X]
      simp [Category.assoc, ← Functor.map_comp]
    rw [hη']
    simp only [Functor.map_comp, Category.assoc]
    erw [β.naturality (L.mapDerivedCategoryFactorsh.inv.app X)]
    have hw := U.mapDerivedCategoryFactorsh.hom.naturality
      ((adj.mapHomotopyCategory (.up ℤ)).unit.app X)
    have hw' : U.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((adj.mapHomotopyCategory (.up ℤ)).unit.app X)) =
      U.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map ((U.mapHomotopyCategory (.up ℤ)).map
          ((adj.mapHomotopyCategory (.up ℤ)).unit.app X)) ≫
        U.mapDerivedCategoryFactorsh.inv.app
          ((R.mapHomotopyCategory (.up ℤ)).obj
            ((L.mapHomotopyCategory (.up ℤ)).obj X)) := by
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hw
      rw [← Category.assoc, ← hw]
      simp
    rw [hw']
    simp only [Category.assoc]
    erw [reassoc_of% hβ ((L.mapHomotopyCategory (.up ℤ)).obj X)]
    rw [← DerivedCategory.Qh.map_comp_assoc, hc X, DerivedCategory.Qh.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% R₀.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory a.inv (.up ℤ)).app X)]
    erw [← reassoc_of% hη₀ ((U.mapHomotopyCategory (.up ℤ)).obj X)]
    erw [← reassoc_of% d₀.unit_naturality (U.mapDerivedCategoryFactorsh.hom.app X)]
    simpa only [Functor.map_comp, Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ d₀.unit.app (U.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        R₀.rightDerivedFunctor.map f) (haDi X)
  -- Localization extensionality extends the unit square to all derived objects.
  have hu (M : DerivedCategory C) :
      U.mapDerivedCategory.map (d.unit.app M) ≫ β.app (L.mapDerivedCategory.obj M) =
      d₀.unit.app (U.mapDerivedCategory.obj M) ≫ R₀.rightDerivedFunctor.map (aD.inv.app M) := by
    let τ : U.mapDerivedCategory ⟶ L.mapDerivedCategory ⋙ V.mapDerivedCategory ⋙
        R₀.rightDerivedFunctor :=
      Functor.whiskerRight d.unit U.mapDerivedCategory ≫
        Functor.whiskerLeft L.mapDerivedCategory β
    let σ : U.mapDerivedCategory ⟶ L.mapDerivedCategory ⋙ V.mapDerivedCategory ⋙
        R₀.rightDerivedFunctor :=
      Functor.whiskerLeft U.mapDerivedCategory d₀.unit ≫
        Functor.whiskerRight aD.inv R₀.rightDerivedFunctor
    have heq : τ = σ := Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) hq
    exact congrArg (fun t ↦ t.app M) heq
  -- The unit square determines the mate by naturality and the right triangle law.
  apply NatTrans.ext
  funext N
  change (mateEquiv d d₀ (TwoSquare.mk _ _ _ _ aD.inv)).app N = β.app N
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.comp_map]
  dsimp only [TwoSquare.mk, Functor.comp_obj]
  simp only [Category.id_comp]
  erw [Category.comp_id]
  change d₀.unit.app (U.mapDerivedCategory.obj (R.rightDerivedFunctor.obj N)) ≫
    R₀.rightDerivedFunctor.map (aD.inv.app (R.rightDerivedFunctor.obj N)) ≫
    R₀.rightDerivedFunctor.map (V.mapDerivedCategory.map (d.counit.app N)) = β.app N
  rw [← Category.assoc, ← hu (R.rightDerivedFunctor.obj N), Category.assoc]
  erw [← β.naturality (d.counit.app N)]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, d.right_triangle_components]
  erw [Functor.map_id, Category.id_comp]
  rfl

end CategoryTheory.Adjunction
