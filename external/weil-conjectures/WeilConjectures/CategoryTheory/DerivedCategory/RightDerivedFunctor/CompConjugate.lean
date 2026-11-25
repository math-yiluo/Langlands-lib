/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-!
# The composition isomorphism of right derived functors is a conjugate

Let `adj₁ : L₁ ⊣ F`, `adj₂ : L₂ ⊣ G` and `adj : L ⊣ H` be adjunctions of additive functors
between abelian categories with exact left adjoints, and let `e : F ⋙ G ≅ H` be the conjugate
of an isomorphism `eL : L ≅ L₂ ⋙ L₁`. Then the composition isomorphism
`RF ⋙ RG ≅ RH` (`CategoryTheory.Functor.rightDerivedFunctorCompIso'`) is the conjugate of the
isomorphism `D(L) ≅ D(L₂) ⋙ D(L₁)` induced by `eL`, under the derived adjunctions
(`CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv`).
-/

@[expose] public section

universe v u₁ u₂ u₃

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesKInjectiveComplexes]
  {L₁ : D ⥤ C} {L₂ : E ⥤ D} {L : E ⥤ C} [L₁.Additive] [L₂.Additive] [L.Additive]
  [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj₁ : L₁ ⊣ F) (adj₂ : L₂ ⊣ G) (adj : L ⊣ H)

/-- The composition isomorphism `RF ⋙ RG ≅ RH` attached to the conjugate `e` of
`eL : L ≅ L₂ ⋙ L₁` is the conjugate of `D(L) ≅ D(L₂) ⋙ D(L₁)`. -/
lemma rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv (e : F ⋙ G ≅ H) (eL : L ≅ L₂ ⋙ L₁)
    (he : e.hom = conjugateEquiv (adj₂.comp adj₁) adj eL.hom) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom =
      conjugateEquiv (adj₂.mapDerivedCategoryRightDerivedAdjunction.comp
          adj₁.mapDerivedCategoryRightDerivedAdjunction)
        adj.mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategoryNatIso eL ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom := by
  apply (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).rightDerived_ext
    (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ))
  ext X
  have hL : (Functor.rightDerivedFunctorCompUnit F G).app X ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj X) =
        (Functor.rightDerivedFunctorUnit (F ⋙ G)).app X ≫
          (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Qh.obj X) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [hL]
  simp only [Functor.comp_obj, Iso.trans_hom, conjugateEquiv_apply_app, NatTrans.comp_app,
    Functor.map_comp, comp_counit_app, Category.assoc, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedNatTrans_app, Functor.whiskerRight_app, NatTrans.mapHomotopyCategory_app]
  erw [adj.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  let Z := ((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj X
  let m : (L.mapHomotopyCategory (.up ℤ)).obj Z ⟶ X :=
    (NatTrans.mapHomotopyCategory eL.hom (.up ℤ)).app Z ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L₂ ⋙ L₁)) (.up ℤ)).hom.app Z ≫
      (L₁.mapHomotopyCategory (.up ℤ)).map ((L₂.mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X)) ≫
      (L₁.mapHomotopyCategory (.up ℤ)).map
        ((adj₂.mapHomotopyCategory (.up ℤ)).counit.app ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      (adj₁.mapHomotopyCategory (.up ℤ)).counit.app X
  have hη : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj Z) ≫
      H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app Z) =
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app Z) ≫
          H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj Z) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso E (.up ℤ))
      L.mapDerivedCategoryFactorsh.hom H.rightDerivedFunctorUnit Z
  have hB : L.mapDerivedCategoryFactorsh.inv.app Z ≫
      L.mapDerivedCategory.map ((Functor.rightDerivedFunctorCompUnit F G).app X) ≫
        (Functor.mapDerivedCategoryNatIso eL).hom.app
          (G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X))) ≫
        (L₂.mapDerivedCategoryCompIso L₁).inv.app
          (G.rightDerivedFunctor.obj (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X))) ≫
        L₁.mapDerivedCategory.map (adj₂.mapDerivedCategoryRightDerivedAdjunction.counit.app
          (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X))) ≫
        adj₁.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map m := by
    have hσ : ∀ {a b : DerivedCategory E} (f : a ⟶ b),
        L.mapDerivedCategory.map f ≫ (Functor.mapDerivedCategoryNatIso eL).hom.app b ≫
          (L₂.mapDerivedCategoryCompIso L₁).inv.app b =
        (Functor.mapDerivedCategoryNatIso eL).hom.app a ≫
          (L₂.mapDerivedCategoryCompIso L₁).inv.app a ≫
            L₁.mapDerivedCategory.map (L₂.mapDerivedCategory.map f) := by
      intro a b f
      rw [NatTrans.naturality_assoc, NatTrans.naturality]
      rfl
    have hcU : (Functor.rightDerivedFunctorCompUnit F G).app X =
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X) ≫
          G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
          G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
      simp [Functor.rightDerivedFunctorCompUnit]
    have hε₁ : L₁.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app X) ≫
        adj₁.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj X) =
          L₁.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
            DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).counit.app X) :=
      (adj₁.mapHomotopyCategory (.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso C (.up ℤ))
        L₁.mapDerivedCategoryFactorsh.hom F.rightDerivedFunctorUnit X
    have hε₂ : L₂.mapDerivedCategory.map
        (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        adj₂.mapDerivedCategoryRightDerivedAdjunction.counit.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj X)) =
          L₂.mapDerivedCategoryFactorsh.hom.app
              ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
            DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).counit.app
              ((F.mapHomotopyCategory (.up ℤ)).obj X)) :=
      (adj₂.mapHomotopyCategory (.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso D (.up ℤ))
        L₂.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnit _
    erw [reassoc_of% hσ]
    rw [hcU]
    have h₂ : L₂.mapDerivedCategory.map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X) ≫
          G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
          G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X)) ≫
        adj₂.mapDerivedCategoryRightDerivedAdjunction.counit.app
          (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X)) =
        L₂.mapDerivedCategory.map (DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X)) ≫
          L₂.mapDerivedCategoryFactorsh.hom.app
              ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
            DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).counit.app
              ((F.mapHomotopyCategory (.up ℤ)).obj X)) ≫
          F.rightDerivedFunctorUnit.app X := by
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
      erw [adj₂.mapDerivedCategoryRightDerivedAdjunction.counit.naturality
        (F.rightDerivedFunctorUnit.app X)]
      erw [reassoc_of% hε₂]
      rfl
    rw [← Functor.map_comp_assoc, h₂]
    simp only [Functor.map_comp, Category.assoc]
    erw [hε₁]
    erw [L₁.mapDerivedCategoryFactorsh.hom.naturality_assoc]
    rw [← Functor.map_comp_assoc L₁.mapDerivedCategory]
    erw [L₂.mapDerivedCategoryFactorsh.hom.naturality]
    rw [Functor.comp_map, Functor.map_comp, Category.assoc]
    erw [L₁.mapDerivedCategoryFactorsh.hom.naturality_assoc]
    have hc := Functor.mapDerivedCategoryCompIso_fach L₂ L₁ Z
    rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
    erw [reassoc_of% hc, reassoc_of% (Functor.mapDerivedCategoryNatIso_fach eL Z),
      Iso.inv_hom_id_app_assoc]
    simp only [m, Functor.comp_map, Functor.map_comp,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.id_comp]
  have hK : (HomotopyCategory.quotient E (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app X.as) =
        (adj.mapHomotopyCategory (.up ℤ)).unit.app Z ≫ (H.mapHomotopyCategory (.up ℤ)).map m := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have hu := mapHomotopyCategory_unit_app_quotient (c := .up ℤ) adj
      (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K)
    have hc₁ := mapHomotopyCategory_counit_app_quotient (c := .up ℤ) adj₁ K
    have hc₂ := mapHomotopyCategory_counit_app_quotient (c := .up ℤ) adj₂
      ((F.mapHomologicalComplex (.up ℤ)).obj K)
    simp only [m, Functor.map_comp]
    erw [hu, hc₁, hc₂, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    refine Eq.trans (b := (HomotopyCategory.quotient E (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app
          (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eL.hom (.up ℤ)).app
              (((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj K) ≫
            (L₁.mapHomologicalComplex (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).counit.app
              ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
            (adj₁.mapHomologicalComplex (.up ℤ)).counit.app K))) ?_ ?_
    · congr 1
      ext n
      simp [he, conjugateEquiv_apply_app, Adjunction.comp_counit_app]
      rfl
    · have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj K) = 𝟙 _ := by
        rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj K)), Iso.hom_inv_id_app,
          Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
      rw [hi]
      simp only [Functor.map_comp]
      repeat erw [CategoryTheory.Functor.map_id]
      simp only [Category.id_comp]
      rfl
  rw [hK, Functor.map_comp, Category.assoc]
  erw [H.rightDerivedFunctorUnit.naturality m]
  rw [Functor.comp_map, ← reassoc_of% hη, ← hB, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rfl

end CategoryTheory.Adjunction
