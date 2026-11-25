/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryStrictSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# Universality of localized strict arrows

Let `adj : E ⊣ r` be an adjunction between abelian categories, where `r` is exact and `E`
preserves quasi-isomorphisms between K-flat complexes. On a K-flat complex `K`, the localized
unit `Q(K) ⟶ D(r)(Q(E(K)))` is a universal arrow to `D(r)`: it is the unit of the derived
adjunction, up to the counit of the left derived functor of `E` at `K`.

Consequently, for a termwise arrow `δ : Φ₁ ⟶ Φ₀ ⋙ r` whose transposes are invertible on the
terms of a complex `P` with `Φ₁(P)` K-flat, the localized arrow
`Functor.strictSquareArrow Φ₁ Φ₀ r δ P` is universal.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Functor

variable {A₁ A₀ : Type*} [Category A₁] [Category A₀] [Abelian A₁] [Abelian A₀]
  [MonoidalCategory A₁] [MonoidalPreadditive A₁]
  [HasCountableCoproducts A₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A₁] [HasExactColimitsOfShape ℤ A₁]
  [∀ (X : A₁), PreservesColimitsOfShape ℤ ((curriedTensor A₁).obj X)]
  [∀ (X : A₁), PreservesColimitsOfShape ℤ ((curriedTensor A₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A₁]
  [HasDerivedCategory A₁] [HasDerivedCategory A₀] [HasKInjectiveResolutions A₀]
  {E : A₁ ⥤ A₀} {r : A₀ ⥤ A₁} [E.Additive] [r.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- On a K-flat complex, the localized unit of an adjunction `E ⊣ r` with `r` exact is a
universal arrow to the derived functor of `r`. -/
theorem isUniversal_localizedUnit (adj : E ⊣ r) (K : CochainComplex A₁ ℤ)
    (hK : (HomologicalComplex.quasiIso A₁ (.up ℤ)).kFlat K) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        r.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K)) :
      StructuredArrow (DerivedCategory.Q.obj K) r.mapDerivedCategory)) := by
  have hα := E.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  let ι := r.rightDerivedFunctorIsoMapDerivedCategory
  let adjD : E.leftDerivedFunctor ⊣ r.mapDerivedCategory := adj.derivedAdjunction.ofNatIsoRight ι
  let X := (HomotopyCategory.quotient A₁ (.up ℤ)).obj K
  let EK := (E.mapHomologicalComplex (.up ℤ)).obj K
  let EX := (E.mapHomotopyCategory (.up ℤ)).obj X
  let c₀ : DerivedCategory.Qh.obj EX ≅ DerivedCategory.Q.obj EK :=
    (DerivedCategory.quotientCompQhIso A₀).app EK
  let g : E.leftDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj EK :=
    E.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso A₁).app K).symm ≪≫
      asIso (E.leftDerivedFunctorCounit.app X) ≪≫ c₀
  have h₁ := adj.derivedAdjunction_unit_app_Qh_fac X
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h₁
  have h₂ : r.rightDerivedFunctorUnit.app EX ≫ ι.hom.app (DerivedCategory.Qh.obj EX) =
      r.mapDerivedCategoryFactorsh.inv.app EX :=
    NatTrans.congr_app r.rightDerivedFunctorIsoMapDerivedCategory_hom_fac _
  have h₃ := adjD.unit.naturality ((DerivedCategory.quotientCompQhIso A₁).hom.app K)
  have h₄ := ι.hom.naturality (E.leftDerivedFunctorCounit.app X)
  have h₅ := r.mapDerivedCategoryFactorsh_hom_app EK
  have h₆ := DerivedCategory.quotientCompQhIso_inv_naturality
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj] at h₄ h₆
  have hu : adjD.unit.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.quotientCompQhIso A₁).inv.app K ≫
        adjD.unit.app (DerivedCategory.Qh.obj X) ≫ r.mapDerivedCategory.map
          (E.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A₁).hom.app K)) := by
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso A₁).hom.app K),
      Iso.hom_inv_id_app_assoc]
    exact h₃
  have h₅' : r.mapDerivedCategoryFactorsh.inv.app EX =
      DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (.up ℤ)).hom.app EK) ≫
        (DerivedCategory.quotientCompQhIso A₁).hom.app ((r.mapHomologicalComplex (.up ℤ)).obj EK) ≫
        r.mapDerivedCategoryFactors.inv.app EK ≫
          r.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A₀).inv.app EK) := by
    rw [← cancel_epi (r.mapDerivedCategoryFactorsh.hom.app EX), Iso.hom_inv_id_app]
    erw [h₅]
    simp only [Category.assoc]
    have q : DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (.up ℤ)).inv.app EK) ≫
        DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (.up ℤ)).hom.app EK) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
    rw [reassoc_of% q, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, Functor.map_id]
    rfl
  have e : DerivedCategory.Qh.map ((r.mapHomotopyCategoryFactors (.up ℤ)).hom.app EK) = 𝟙 _ := by
    rw [show (r.mapHomotopyCategoryFactors (.up ℤ)).hom.app EK = 𝟙 _ from rfl]
    exact Functor.map_id _ _
  have he : adjD.unit.app (DerivedCategory.Q.obj K) ≫ r.mapDerivedCategory.map g.hom =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        r.mapDerivedCategoryFactors.inv.app EK := by
    rw [hu]
    simp only [g, adjD, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Iso.app_inv,
      Functor.map_comp, Category.assoc]
    have k₁ : r.mapDerivedCategory.map
          (E.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A₁).hom.app K)) ≫
        r.mapDerivedCategory.map
          (E.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A₁).inv.app K)) =
        𝟙 _ := by
      simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
    rw [reassoc_of% k₁, ← reassoc_of% h₄, reassoc_of% h₁, reassoc_of% h₂, h₅',
      e, Category.id_comp, ← reassoc_of% h₆]
    simp only [Category.assoc, c₀, Iso.app_hom, ← Functor.map_comp, Iso.inv_hom_id_app,
      Functor.map_id]
    erw [Iso.inv_hom_id_app_assoc, Category.comp_id]
  exact ⟨(mkInitialOfLeftAdjoint _ adjD _).ofIso (StructuredArrow.isoMk g he)⟩

variable {C : Type*} [Category C] [Preadditive C] (Φ₁ : C ⥤ A₁) (Φ₀ : C ⥤ A₀)
  [Φ₁.Additive] [Φ₀.Additive]

/-- A localized termwise arrow `δ : Φ₁ ⟶ Φ₀ ⋙ r` is universal on a complex `P` when `Φ₁(P)` is
K-flat and the transposes of `δ` under `E ⊣ r` are invertible on the terms of `P`. -/
theorem strictSquareArrow_isUniversal (adj : E ⊣ r) (δ : Φ₁ ⟶ Φ₀ ⋙ r)
    (P : CochainComplex C ℤ)
    (hK : (HomologicalComplex.quasiIso A₁ (.up ℤ)).kFlat
      ((Φ₁.mapHomologicalComplex (.up ℤ)).obj P))
    (hδ : ∀ i, IsIso ((adj.homEquiv _ _).symm (δ.app (P.X i)))) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (strictSquareArrow Φ₁ Φ₀ r δ P))) := by
  let K := (Φ₁.mapHomologicalComplex (.up ℤ)).obj P
  let M := (Φ₀.mapHomologicalComplex (.up ℤ)).obj P
  let adjC := adj.mapHomologicalComplex (.up ℤ)
  let a : K ⟶ (r.mapHomologicalComplex (.up ℤ)).obj M :=
    (NatTrans.mapHomologicalComplex δ (ComplexShape.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso (F := Φ₀) (G := r) (Iso.refl _)
        (ComplexShape.up ℤ)).inv.app P
  let t : (E.mapHomologicalComplex (.up ℤ)).obj K ⟶ M := (adjC.homEquiv K M).symm a
  have ha : a = adjC.unit.app K ≫ (r.mapHomologicalComplex (.up ℤ)).map t :=
    ((adjC.homEquiv_unit K M t).symm.trans ((adjC.homEquiv K M).apply_symm_apply a)).symm
  have ht : IsIso t := by
    have : ∀ i, IsIso (t.f i) := fun i ↦ by
      have h := hδ i
      rw [Adjunction.homEquiv_counit] at h
      have e : t.f i = E.map (δ.app (P.X i)) ≫ adj.counit.app (Φ₀.obj (P.X i)) := by
        simp only [t, Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
          Functor.mapHomologicalComplex_map_f]
        congr 1
        simp only [a, HomologicalComplex.comp_f, Functor.map_comp]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        rfl
      rw [e]
      exact h
    exact HomologicalComplex.Hom.isIso_of_components t
  have key : strictSquareArrow Φ₁ Φ₀ r δ P =
      (DerivedCategory.Q.map (adjC.unit.app K) ≫
        r.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K)) ≫
          r.mapDerivedCategory.map (DerivedCategory.Q.map t) := by
    change DerivedCategory.Q.map a ≫ _ = _
    rw [ha, Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact r.mapDerivedCategoryFactors.inv.naturality t
  obtain ⟨hu⟩ := isUniversal_localizedUnit adj K hK
  exact ⟨hu.ofIso (StructuredArrow.isoMk (asIso (DerivedCategory.Q.map t)) key.symm)⟩

end CategoryTheory.Functor
