/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! Derived counit normalization for a fixed sectionwise scalar model.

## References

* Stacks 06YY and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

-- Precomposition preserves the universal property whenever natural transformations
-- descend uniquely; this includes the quotient from complexes to homotopy classes.
private theorem kan_precomp
    {A C D H : Type*} [Category* A] [Category* C] [Category* D] [Category* H]
    (P : A ⥤ C) [((Functor.whiskeringLeft A C H).obj P).Full]
    [((Functor.whiskeringLeft A C H).obj P).Faithful]
    (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H) (α : Q ⋙ L ⟶ F)
    [L.IsRightKanExtension α] :
    L.IsRightKanExtension
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α) := by
  let R := Functor.RightExtension.precomp Q F P
  have : R.IsEquivalence := by
    let W := (Functor.whiskeringLeft A C H).obj P
    let U := (Functor.whiskeringLeft A D H).obj (P ⋙ Q)
    have : IsIso (𝟙 (P ⋙ F)) := IsIso.id _
    have : IsIso (𝟙 U) := IsIso.id _
    exact CostructuredArrow.isEquivalenceMap₂
      (S := (Functor.whiskeringLeft C D H).obj Q) (U := U)
      (F := 𝟭 (D ⥤ H)) (G := W) (𝟙 U) (𝟙 (P ⋙ F))
  have h := (IsTerminal.isTerminalIffObj R (Functor.RightExtension.mk L α)).1
    (L.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl _) (by
    ext X
    simp [R, Functor.RightExtension.precomp]))⟩⟩

-- Equivalences of the output category preserve universal right extensions.
private theorem kan_postcomp
    {C D H H' : Type*} [Category* C] [Category* D] [Category* H] [Category* H']
    (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H) (α : Q ⋙ L ⟶ F)
    [L.IsRightKanExtension α] (E : H ⥤ H') [E.IsEquivalence] :
    (L ⋙ E).IsRightKanExtension
      ((Functor.associator Q L E).inv ≫ Functor.whiskerRight α E) := by
  let R := Functor.RightExtension.postcompose₂ Q F E
  have : R.IsEquivalence := by
    let i : ((Functor.whiskeringRight D H H').obj E) ⋙
          (Functor.whiskeringLeft C D H').obj Q ≅
        (Functor.whiskeringLeft C D H).obj Q ⋙
          (Functor.whiskeringRight C H H').obj E :=
      NatIso.ofComponents (fun L ↦ (Functor.associator Q L E).symm)
    change (CostructuredArrow.map₂ i.hom (𝟙 (F ⋙ E))).IsEquivalence
    have : IsIso (𝟙 (F ⋙ E)) := IsIso.id _
    exact CostructuredArrow.isEquivalenceMap₂ _ _
  have h := (IsTerminal.isTerminalIffObj R (Functor.RightExtension.mk L α)).1
    (L.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (Functor.RightExtension.postcompose₂ObjMkIso E α)⟩⟩

private theorem map_id_cleanup
    {A C H : Type*} [Category* A] [Category* C] [Category* H]
    (F : A ⥤ H) (G : C ⥤ H) {X : A} {Y : C} (f : F.obj X ⟶ G.obj Y) :
    F.map (𝟙 X) ≫ f ≫ G.map (𝟙 Y) ≫ 𝟙 _ = f := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, CategoryTheory.Category.comp_id]

private theorem four_comp_id
    {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ : C}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (k : X₃ ⟶ X₄) :
    f ≫ g ≫ h ≫ k ≫ 𝟙 X₄ = f ≫ g ≫ h ≫ k := by
  rw [CategoryTheory.Category.comp_id]

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

attribute [local instance] ModuleRingedComparison.sectionFunctorAdditive

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- A fixed sectionwise model admits a derived comparison normalized by its counit. -/
theorem scalar_section_derived_comparison_exists (T : Scheme.{u})
    (model : SectionModel a T)
    (ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E) :
    ∃ derived : D a T ⋙ derivedFunctor Λ' T ≅
        derivedFunctor Λ T ⋙ model.T,
      ∀ P : CochainComplex (Modules Λ T) ℤ,
        derived.hom.app (DerivedCategory.Q.obj P) ≫
            model.T.map (sectionLocalizationComparison Λ T P).hom ≫
            model.ε.app
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) =
          (derivedFunctor Λ' T).map (compute a T P) ≫
            (sectionLocalizationComparison Λ' T
              (((QuotientChange.extension a T).mapHomologicalComplex
                (.up ℤ)).obj P)).hom ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (Iso.refl ((equivalence Λ T).functor ⋙ model.E)) (.up ℤ)).inv.app P) := by
  classical
  let ER := (equivalence Λ T).functor
  let ES := (equivalence Λ' T).functor
  let ec := (equivalence Λ T).mapHomologicalComplex (.up ℤ)
  let F := (QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)
  let q := HomotopyCategory.quotient (Modules Λ T) (.up ℤ)
  have hD : (D a T).IsLeftDerivedFunctor (scalarCounit a T)
      (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)) := by
    unfold D scalarCounit
    dsimp only [Functor.leftDerivedFunctor, Functor.leftDerivedFunctorCounit, id]
    infer_instance
  have : (D a T).IsRightKanExtension (scalarCounit a T) :=
    hD.isRightKanExtension
  let α := (Functor.associator q DerivedCategory.Qh (D a T)).hom ≫
    Functor.whiskerLeft q (scalarCounit a T)
  have : (D a T).IsRightKanExtension α :=
    kan_precomp q _ _ _ (scalarCounit a T)
  let γ := Functor.mapHomologicalComplexCompIso ordinary (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (ER ⋙ model.E)) (.up ℤ)).symm
  let τ : (F ⋙ DerivedCategory.Q) ⋙ derivedFunctor Λ' T ≅
      ec.functor ⋙ model.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F ES.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight γ DerivedCategory.Q ≪≫ Functor.associator _ _ _
  let α₀ := (Functor.associator DerivedCategory.Q (D a T) (derivedFunctor Λ' T)).inv ≫
    Functor.whiskerRight α (derivedFunctor Λ' T)
  have : (D a T ⋙ derivedFunctor Λ' T).IsRightKanExtension α₀ :=
    kan_postcomp _ _ _ α (derivedFunctor Λ' T)
  let α' := α₀ ≫ τ.hom
  have : (D a T ⋙ derivedFunctor Λ' T).IsRightKanExtension α' :=
    (Functor.isRightKanExtension_iff_of_iso₂ α₀ α' τ (Iso.refl _)
      (by simp [α'])).1 inferInstance
  have : model.T.IsRightKanExtension model.ε := model.universal.isRightKanExtension
  let β₀ := (Functor.associator ec.functor DerivedCategory.Q model.T).hom ≫
    Functor.whiskerLeft ec.functor model.ε
  have : model.T.IsRightKanExtension β₀ :=
    kan_precomp ec.functor _ _ _ model.ε
  have hβ₀ : model.T.IsRightKanExtension β₀ := inferInstance
  let β := (Functor.associator DerivedCategory.Q (derivedFunctor Λ T) model.T).inv ≫
    Functor.whiskerRight ER.mapDerivedCategoryFactors.hom model.T ≫ β₀
  have : (derivedFunctor Λ T ⋙ model.T).IsRightKanExtension β :=
    (Functor.isRightKanExtension_iff_postcomp₁ (derivedFunctor Λ T)
      ER.mapDerivedCategoryFactors β₀).1 hβ₀
  let e := Functor.rightKanExtensionUnique (D a T ⋙ derivedFunctor Λ' T) α'
    (derivedFunctor Λ T ⋙ model.T) β
  refine ⟨e, ?_⟩
  intro P
  have h : e.hom.app (DerivedCategory.Q.obj P) ≫ β.app P = α'.app P := by
    simpa only [e, Functor.rightKanExtensionUnique,
      Functor.rightKanExtensionUniqueOfIso_hom, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Category.comp_id] using Functor.liftOfIsRightKanExtension_fac_app
        (derivedFunctor Λ T ⋙ model.T) β (D a T ⋙ derivedFunctor Λ' T) α' P
  have hc : compute a T P = (scalarCounit a T).app (q.obj P) := by
    unfold compute
    change (D a T).map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
    exact map_id_cleanup (D a T) DerivedCategory.Qh _
  simp only [α', α₀, α, β, β₀, τ, γ, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.map_comp, Category.id_comp, Functor.comp_obj,
    sectionLocalizationComparison, Iso.app_hom, hc, Category.assoc] at h ⊢
  erw [Category.id_comp] at h
  set_option backward.isDefEq.respectTransparency false in
    simpa only [ec, Equivalence.mapHomologicalComplex_functor, ER, ES, F,
      Category.id_comp, Category.comp_id] using h

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
