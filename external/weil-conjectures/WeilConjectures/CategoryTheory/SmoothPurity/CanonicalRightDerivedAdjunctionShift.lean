/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Canonical unbounded derived adjunctions commute with shifts

Source: Stacks Project, Tags 07A6 and 0DVC. The proof uses the normalized-unit
argument from DerivedAdjunctionShift and the K-injective unit calculation from
RestrictedDerivedSectionsShiftTransport, without their geometric specializations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory

private theorem rightKan_postadjoint_ext
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (F : A ⥤ C) (LF : B ⥤ C) (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] (T : D ⥤ C) (S : C ⥤ D) (a : T ⊣ S)
    (H : B ⥤ D) (γ₁ γ₂ : H ⟶ LF ⋙ S)
    (h : ∀ X, γ₁.app (Q.obj X) ≫ S.map (α.app X) =
      γ₂.app (Q.obj X) ≫ S.map (α.app X)) : γ₁ = γ₂ := by
  apply ((a.whiskerRight B).homEquiv H LF).symm.injective
  apply LF.hom_ext_of_isRightKanExtension α
  simp only [Adjunction.homEquiv_counit]
  ext X
  have hx := congrArg ((a.homEquiv (H.obj (Q.obj X)) (F.obj X)).symm) (h X)
  simpa [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    ← a.counit.naturality, Adjunction.whiskerRight_counit_app_app] using hx

private theorem rightKan_postadjoint_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (F : A ⥤ C) [F.CommShift ℤ]
    (LF : B ⥤ C) [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (T : D ⥤ C) (S : C ⥤ D) [S.CommShift ℤ] (a : T ⊣ S)
    (H : B ⥤ D) [H.CommShift ℤ] (τ : H ⟶ LF ⋙ S)
    [NatTrans.CommShift (Functor.whiskerLeft Q τ ≫
      (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S) ℤ] :
    NatTrans.CommShift τ ℤ := by
  let δ := (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S
  have : NatTrans.CommShift δ ℤ := by dsimp [δ]; infer_instance
  have hτ : NatTrans.CommShift (Functor.whiskerLeft Q τ ≫ δ) ℤ := by assumption
  constructor
  intro n
  apply rightKan_postadjoint_ext Q F LF α
    ((shiftEquiv D n).symm.functor ⋙ T) (S ⋙ shiftFunctor D n)
    ((shiftEquiv D n).symm.toAdjunction.comp a)
  intro X
  have hdapp (Y : A) : δ.app Y = S.map (α.app Y) := by
    simp [δ]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, ← hdapp X]
  apply (cancel_epi (H.map ((Q.commShiftIso n).hom.app X))).mp
  have hd := NatTrans.shift_app_comm δ n X
  have ht := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ ≫ δ) n X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc] at ht
  rw [← hd] at ht
  have hn := τ.naturality ((Q.commShiftIso n).hom.app X)
  dsimp at hn
  have hn' := congrArg (fun f ↦ f ≫ ((LF ⋙ S).commShiftIso n).hom.app (Q.obj X) ≫
    (shiftFunctor D n).map (δ.app X)) hn
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc, Functor.comp_map] at ht
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hn' ⊢
  exact ht.trans hn'.symm

private theorem normalized_unit_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (QA : A ⥤ C) (QB : B ⥤ D) [QA.CommShift ℤ] [QB.CommShift ℤ]
    (F : A ⥤ B) (G : B ⥤ A) [F.CommShift ℤ] [G.CommShift ℤ]
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    (ah : F ⊣ G) [NatTrans.CommShift ah.unit ℤ] (adj : L ⊣ R)
    (α : QA ⋙ L ⟶ F ⋙ QB) (β : G ⋙ QA ⟶ QB ⋙ R)
    [L.IsRightKanExtension α] [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ]
    (hnorm : ∀ M, adj.unit.app (QA.obj M) ≫ R.map (α.app M) =
      QA.map (ah.unit.app M) ≫ β.app (F.obj M)) :
    NatTrans.CommShift adj.unit ℤ := by
  let δ := Functor.whiskerLeft QA adj.unit ≫
    (Functor.associator QA L R).inv ≫ Functor.whiskerRight α R
  have heq : δ =
      (Functor.rightUnitor QA).hom ≫ (Functor.leftUnitor QA).inv ≫
      Functor.whiskerRight ah.unit QA ≫ (Functor.associator F G QA).hom ≫
      Functor.whiskerLeft F β ≫ (Functor.associator F QB R).inv := by
    ext M
    simpa [δ] using hnorm M
  have hδ : NatTrans.CommShift δ ℤ := by
    rw [heq]
    infer_instance
  exact rightKan_postadjoint_commShift QA _ L α L R adj (𝟭 _) adj.unit

private theorem canonical_unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

/-- The adjunction induced by an exact left adjoint and the canonical K-injective
right-derived functor respects their canonical shifts.
Source: Stacks Project, Tags 07A6 and 0DVC.
(blueprint: lem-sp-canonical-right-derived-adjunction-shift).

Proof: on K-injective complexes the canonical derived unit is invertible, and
its comparison with the K-injective equivalence makes it commute with shifts.
Every homotopy object admits a quasi-isomorphism into a K-injective complex,
so the same holds for the unit on all objects. The unit of the derived adjunction
satisfies the universal derived-unit factorization. Its right side is built from
the ordinary adjunction unit and the canonical derived unit, both compatible with
shifts. The right Kan universal property, after the adjoint postcomposition,
detects equality of these shift squares. Hence the derived adjunction unit
commutes with shifts; the triangle identities imply the same for its counit. -/
theorem canonicalRightDerivedAdjunctionShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    adj.mapDerivedCategoryRightDerivedAdjunction.CommShift ℤ := by
  let ah := adj.mapHomotopyCategory (.up ℤ)
  let ad := adj.mapDerivedCategoryRightDerivedAdjunction
  let : L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    Adjunction.isLeftDerivedFunctor_mapDerivedCategory
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension L.mapDerivedCategory
    L.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C (.up ℤ))
  have hβ : NatTrans.CommShift R.rightDerivedFunctorUnit ℤ := canonical_unit_commShift R
  let := hβ
  have hn (M : HomotopyCategory C (.up ℤ)) :
      ad.unit.app (DerivedCategory.Qh.obj M) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app M) =
      DerivedCategory.Qh.map (ah.unit.app M) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj M) := by
    exact ah.derivedη_fac_app (HomotopyCategory.quasiIso C (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit M
  have hu : NatTrans.CommShift ad.unit ℤ :=
    normalized_unit_commShift DerivedCategory.Qh DerivedCategory.Qh
      (L.mapHomotopyCategory (.up ℤ)) (R.mapHomotopyCategory (.up ℤ))
      L.mapDerivedCategory R.rightDerivedFunctor ah ad
      L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit hn
  exact Adjunction.CommShift.mk' ad ℤ hu

end CategoryTheory
