/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # The finite projection of the quotient completion unit

Source: Stacks Tags 0941, 099M, 06YY.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.AdicSites

attribute [local irreducible] constantSheaf HasDerivedCategory.standard

private instance ordinaryLimit_additive (S : Site.{u}) (A : Type u) [CommRing A] :
    (lim : S.towers A ⥤ S.modules A).Additive :=
  (constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
    (lim : S.towers A ⥤ S.modules A)).right_adjoint_additive

private abbrev diagonal (S : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :
    S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
    Functor.mapDerivedCategoryIdIso (S.modules A)

private abbrev π (S : Site.{u}) (A : Type u) [CommRing A]
    (X : S.towerDerived A) (n : ℕ) : (S.rlim A).obj X ⟶ (S.evaluate A n).obj X :=
  (diagonal S A n).inv.app ((S.rlim A).obj X) ≫
    (S.evaluate A n).map ((S.deltaAdjunction A).counit.app X)

private theorem limitComparison_counit (S : Site.{u}) (A : Type u) [CommRing A]
    (X : CochainComplex (S.towers A) ℤ) :
    (S.delta A).map ((ConstantCompletion.limitComparison (S.ring A)).app X) ≫
        (S.deltaAdjunction A).counit.app ((ConstantCompletion.TQ (S.ring A)).obj X) =
      (ConstantCompletion.constantTower S.topology (S.ring A)).mapDerivedCategoryFactors.hom.app
          ((ConstantCompletion.ordinaryLimit (S.ring A)).obj X) ≫
        (ConstantCompletion.TQ (S.ring A)).map
          (((constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
            (lim : S.towers A ⥤ S.modules A)).mapHomologicalComplex (.up ℤ)).counit.app X) := by
  let ad := S.deltaAdjunction A
  let ad₀ := (constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
    (lim : S.towers A ⥤ S.modules A)).mapHomologicalComplex (.up ℤ)
  apply (ad.homEquiv _ _).injective
  erw [← ad.homEquiv_counit, Equiv.apply_symm_apply, ad.homEquiv_unit]
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
  have hn := (S.deltaAdjunction_existsUnique A).exists.choose_spec
    ((ConstantCompletion.ordinaryLimit (S.ring A)).obj X)
  change ad.unit.app _ ≫ (S.rlim A).map _ = _ at hn
  dsimp only [Functor.comp_obj]
  rw [hn, Category.assoc]
  have hnat := (ConstantCompletion.limitComparison (S.ring A)).naturality (ad₀.counit.app X)
  change (ConstantCompletion.Q (S.ring A)).map
    ((ConstantCompletion.ordinaryLimit (S.ring A)).map (ad₀.counit.app X)) ≫ _ =
      _ ≫ (S.rlim A).map ((ConstantCompletion.TQ (S.ring A)).map (ad₀.counit.app X)) at hnat
  dsimp only [Functor.comp_obj, Functor.id_obj, ad₀] at hnat
  erw [← hnat, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  have ht := ad₀.right_triangle_components X
  change ad₀.unit.app _ ≫
    (ConstantCompletion.ordinaryLimit (S.ring A)).map (ad₀.counit.app X) = 𝟙 _ at ht
  erw [ht, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem derived_id_factors (S : Site.{u}) (A : Type u) [CommRing A]
    (P : CochainComplex (S.modules A) ℤ) :
    (Functor.mapDerivedCategoryIdIso (S.modules A)).hom.app
        ((ConstantCompletion.Q (S.ring A)).obj P) =
      (𝟭 (S.modules A)).mapDerivedCategoryFactors.hom.app P := by
  let q := DerivedCategory.quotientCompQhIso (S.modules A)
  let e := Functor.mapDerivedCategoryIdIso (S.modules A)
  have hn := e.hom.naturality (q.hom.app P)
  dsimp only [Functor.id_map, Functor.comp_obj, e] at hn
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryFactorsh_hom_app] at hn
  have hf : ((𝟭 (S.modules A)).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hh : DerivedCategory.Qh.map
      (((𝟭 (S.modules A)).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) = 𝟙 _ := by
    rw [hf]
    exact DerivedCategory.Qh.map_id _
  rw [hh] at hn
  have hq : (DerivedCategory.quotientCompQhIso (S.modules A)).inv.app
      (((𝟭 (S.modules A)).mapHomologicalComplex (.up ℤ)).obj P) ≫ q.hom.app P = 𝟙 _ := by
    exact Iso.inv_hom_id_app q P
  simp only [Category.assoc] at hn
  erw [Category.id_comp, hq, Category.comp_id] at hn
  exact (cancel_epi ((𝟭 (S.modules A)).mapDerivedCategory.map (q.hom.app P))).mp hn

private theorem diagonal_factors (S : Site.{u}) (A : Type u) [CommRing A]
    (P : CochainComplex (S.modules A) ℤ) (n : ℕ) :
    (show S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) from
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
        Functor.mapDerivedCategoryIdIso (S.modules A)).inv.app
          ((ConstantCompletion.Q (S.ring A)).obj P) ≫
      (S.evaluate A n).map
        ((ConstantCompletion.constantTower S.topology (S.ring A)
          ).mapDerivedCategoryFactors.hom.app P) ≫
      (S.evaluateModule A n).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.constantTower S.topology (S.ring A)).mapHomologicalComplex
          (.up ℤ)).obj P) = 𝟙 _ := by
  let δ := ConstantCompletion.constantTower S.topology (S.ring A)
  let E := S.evaluateModule A n
  have hcomp := Functor.mapDerivedCategoryCompIso_hom_app_factors δ E P
  have hnat := Functor.mapDerivedCategoryNatIso_fac
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl) :
      δ ⋙ E ≅ 𝟭 (S.modules A)) P
  have hh : (NatTrans.mapHomologicalComplex
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl) :
        δ ⋙ E ≅ 𝟭 (S.modules A)).hom (.up ℤ)).app P = 𝟙 _ := by
    ext q
    rfl
  erw [hh, CategoryTheory.Functor.map_id, Category.comp_id] at hnat
  dsimp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, hcomp, ← hnat,
    Iso.inv_hom_id_app_assoc, ← derived_id_factors S A P, Iso.inv_hom_id_app]

private theorem projection_comparison (S : Site.{u}) (A : Type u) [CommRing A]
    (X : CochainComplex (S.towers A) ℤ) (n : ℕ) :
    (ConstantCompletion.limitComparison (S.ring A)).app X ≫
        π S A ((ConstantCompletion.TQ (S.ring A)).obj X) n ≫
        (S.evaluateModule A n).mapDerivedCategoryFactors.hom.app X =
      (ConstantCompletion.Q (S.ring A)).map
        (((S.evaluateModule A n).mapHomologicalComplex (.up ℤ)).map
          (((constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
            (lim : S.towers A ⥤ S.modules A)).mapHomologicalComplex (.up ℤ)).counit.app X)) := by
  let ad₀ := (constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
    (lim : S.towers A ⥤ S.modules A)).mapHomologicalComplex (.up ℤ)
  have hd := (diagonal S A n).inv.naturality
    ((ConstantCompletion.limitComparison (S.ring A)).app X)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hd
  dsimp only [π]
  erw [← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, limitComparison_counit,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  have he := (S.evaluateModule A n).mapDerivedCategoryFactors.hom.naturality
    (ad₀.counit.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  erw [he]
  have hdiag := diagonal_factors S A ((ConstantCompletion.ordinaryLimit (S.ring A)).obj X) n
  dsimp only [diagonal] at hdiag
  erw [reassoc_of% hdiag]

private theorem ordinary_finite_unit (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (M : S.modules A) (n : ℕ) :
    ((ConstantCompletion.reductionUnit S.topology A I false).app M).app
        (Opposite.op n) = (S.finiteModuleAdjunction A I n).unit.app M := by
  let φ := ConstantCompletion.quotient S.topology A I n
  have hr : (ConstantCompletion.underlying (S.ring A)).map
      (((ConstantCompletion.reductionUnit S.topology A I false).app M).app
        (Opposite.op n)) = ConstantCompletion.insertion φ M := by
    apply (ConstantCompletion.insertion_existsUnique φ M).unique
    · intro U m
      exact (ConstantCompletion.reductionUnit_existsUnique S.topology A I false
        ).exists.choose_spec M n U m
    · exact (ConstantCompletion.insertion_existsUnique φ M).exists.choose_spec
  have ha := (S.finiteModuleAdjunction_existsUnique A I n).exists.choose_spec
    M _ (𝟙 _)
  rw [Adjunction.homEquiv_unit] at ha
  erw [CategoryTheory.Functor.map_id, Category.comp_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at ha
  exact (ConstantCompletion.underlying (S.ring A)).map_injective (hr.trans ha.symm)

private theorem limit_counit_app
    {C J : Type*} [Category C] [Category J] [HasLimitsOfShape J C]
    (X : J ⥤ C) (j : J) :
    ((constLimAdj : (Functor.const J : C ⥤ J ⥤ C) ⊣ lim).counit.app X).app j =
      limit.π X j := rfl

private theorem ordinary_projection_unit (S : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (P : CochainComplex (S.modules A) ℤ) (n : ℕ) :
    ConstantCompletion.ordinaryUnit S.topology A I false P ≫
      ((S.evaluateModule A n).mapHomologicalComplex (.up ℤ)).map
        (((constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
          (lim : S.towers A ⥤ S.modules A)).mapHomologicalComplex (.up ℤ)).counit.app
          (ConstantCompletion.reductionComplex S.topology A I false P)) =
      (NatTrans.mapHomologicalComplex (S.finiteModuleAdjunction A I n).unit (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro q
  rw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    NatTrans.mapHomologicalComplex_app_f]
  change (ConstantCompletion.ordinaryUnit S.topology A I false P).f q ≫
    ((constLimAdj : ConstantCompletion.constantTower S.topology (S.ring A) ⊣
      (lim : S.towers A ⥤ S.modules A)).counit.app
        ((ConstantCompletion.reductionComplex S.topology A I false P).X q)).app
          (Opposite.op n) = (S.finiteModuleAdjunction A I n).unit.app (P.X q)
  rw [limit_counit_app]
  exact ((ConstantCompletion.ordinaryUnit_existsUnique S.topology A I false P
    ).exists.choose_spec q n).trans (ordinary_finite_unit S A I (P.X q) n)

private theorem projection_naturality (S : Site.{u}) (A : Type u) [CommRing A]
    {M N : S.towerDerived A} (f : M ⟶ N) (n : ℕ) :
    (S.rlim A).map f ≫ π S A N n =
      π S A M n ≫ (S.evaluate A n).map f := by
  have h := (diagonal S A n).inv.naturality ((S.rlim A).map f)
  change (S.rlim A).map f ≫ (diagonal S A n).inv.app _ =
    (diagonal S A n).inv.app _ ≫
      (S.evaluate A n).map ((S.delta A).map ((S.rlim A).map f)) at h
  have hc := (S.deltaAdjunction A).counit.naturality f
  change (S.delta A).map ((S.rlim A).map f) ≫ _ = _ ≫ f at hc
  dsimp only [π]
  rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp, hc,
    CategoryTheory.Functor.map_comp, Category.assoc]

end CategoryTheory.AdicSites
