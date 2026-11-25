/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-!
# Compatibility of normalized towers with retained étale origins

All finite coefficient categories use their canonical fixed-ring presentation. The
coefficient realization identifies them with modules over the continuous-function coefficient
sheaf on the small pro-étale site. All outputs are ambient derived objects.

## Implementation details

In `PbcWitnessedTower` only adjacent normalization maps are independent data: longer
reductions and their maps are the composites of these, read through the canonical
scalar-extension composition comparisons, so the identity and quotient cocycles are built into
the encoding.

## References

* Stacks Project, Tags 03D2, 06XN, 06YY, 07A4, 099L, 09C2, 09C9, 0G7E
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale

private theorem transport_unit_normalization
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {R R' : B ⥤ A} (d : L ⊣ R) (e : R ≅ R')
    {P M : A} {N : B} (f : L.obj P ⟶ N) (b : R'.obj N ⟶ M)
    (u : P ⟶ M) (v : M ⟶ R.obj N)
    (h : d.unit.app P ≫ R.map f = u ≫ v)
    (hv : v ≫ e.hom.app N ≫ b = 𝟙 M) :
    (d.ofNatIsoRight e).unit.app P ≫ R'.map f ≫ b = u := by
  rw [Adjunction.ofNatIsoRight_unit]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, ← Category.assoc, h]
  simp only [Category.assoc]
  rw [hv, Category.comp_id]

private theorem exists_comparison_kFlat_representative
    {A B : Type*} [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [MonoidalCategory B] [MonoidalPreadditive B] [HasCountableCoproducts B]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor B).obj X)]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor B).flip.obj X)]
    [HasDerivedCategory A] [Abelian.HasFunctorialFlatResolution A]
    (F : A ⥤ B) [F.Additive] [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]
    (X : DerivedCategory A) :
    ∃ M : HomotopyCategory A (.up ℤ),
      (HomotopyCategory.quasiIso A (.up ℤ)).kFlat M ∧
      (HomotopyCategory.quasiIso B (.up ℤ)).kFlat
        ((F.mapHomotopyCategory (.up ℤ)).obj M) ∧ Nonempty (DerivedCategory.Qh.obj M ≅ X) := by
  classical
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) :=
    (inferInstance : Abelian.HasFunctorialFlatResolution A).some.reduced
  let P : CochainComplex A ℤ := (DerivedCategory.Q (C := A)).objPreimage X
  let K : CochainComplex A ℤ := Λ.resolutionFunctor.obj P
  let M : HomotopyCategory A (.up ℤ) := (HomotopyCategory.quotient A (.up ℤ)).obj K
  have hK : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat M :=
    (HomotopyCategory.kFlat_quotient_obj_iff K).2
      (Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le P)
  have hFK₀ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
    F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ
      ObjectProperty.flat.essImage_ι_le P
  have hFK : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((F.mapHomotopyCategory (.up ℤ)).obj M) :=
    ObjectProperty.prop_of_iso (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((F.mapHomotopyCategoryFactors (.up ℤ)).app K).symm
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hFK₀)
  let e : DerivedCategory.Qh.obj M ≅ X :=
    (DerivedCategory.quotientCompQhIso A).app K ≪≫
      asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app P)) ≪≫
        (DerivedCategory.Q (C := A)).objObjPreimageIso X
  exact ⟨M, hK, hFK, ⟨e⟩⟩

private theorem derived_adjunction_unit_normalization
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {E : A ⥤ B} {U : B ⥤ A} [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : E ⊣ U)
    (P : HomotopyCategory A (.up ℤ)) :
    (adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory).unit.app
        (DerivedCategory.Qh.obj P) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app P) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj P) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app P) := by
  let e := U.rightDerivedFunctorIsoMapDerivedCategory
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (L₁ := DerivedCategory.Qh) (L₂ := DerivedCategory.Qh)
    (G' := E.leftDerivedFunctor) (F' := U.rightDerivedFunctor)
    (HomotopyCategory.quasiIso _ (.up ℤ)) E.leftDerivedFunctorCounit
    U.rightDerivedFunctorUnit P
  have he := congr_app U.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((E.mapHomotopyCategory (.up ℤ)).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at he
  have he' : U.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj P) ≫
      e.hom.app (DerivedCategory.Qh.obj ((E.mapHomotopyCategory (.up ℤ)).obj P)) =
      U.mapDerivedCategoryFactorsh.inv.app ((E.mapHomotopyCategory (.up ℤ)).obj P) := he
  have hv : U.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj P) ≫
      e.hom.app (DerivedCategory.Qh.obj ((E.mapHomotopyCategory (.up ℤ)).obj P)) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj P) = 𝟙 _ := by
    rw [← Category.assoc, he']
    exact Iso.inv_hom_id_app _ _
  exact transport_unit_normalization adj.derivedAdjunction e
    (E.leftDerivedFunctorCounit.app P) (U.mapDerivedCategoryFactorsh.hom.app _)
    (DerivedCategory.Qh.map
      ((adj.mapHomotopyCategory (.up ℤ)).unit.app P))
    (U.rightDerivedFunctorUnit.app _) h hv

private structure DerivedAdjunctionWithUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {E : A ⥤ B} {U : B ⥤ A} [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : E ⊣ U) where
  adjunction : E.leftDerivedFunctor ⊣ U.mapDerivedCategory
  unit_formula (P : HomotopyCategory A (.up ℤ)) :
    adjunction.unit.app (DerivedCategory.Qh.obj P) ≫
      U.mapDerivedCategory.map (E.leftDerivedFunctorCounit.app P) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((E.mapHomotopyCategory (.up ℤ)).obj P) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app P)

private noncomputable def normalizedDerivedAdjunction
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {E : A ⥤ B} {U : B ⥤ A} [E.Additive] [U.Additive] [E.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (adj : E ⊣ U) :
    DerivedAdjunctionWithUnit adj :=
  ⟨adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory,
    derived_adjunction_unit_normalization adj⟩

private theorem mate_of_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ C} {H : C ⥤ A} {G : B ⥤ D} {K : D ⥤ B}
    {U₁ : B ⥤ A} {V₁ : A ⥤ B} {U₂ : D ⥤ C} {V₂ : C ⥤ D}
    (a₁ : G ⊣ K) (a₂ : F ⊣ H) (b₁ : U₂ ⊣ V₂) (b₂ : U₁ ⊣ V₁)
    (e : V₂ ⋙ K ≅ H ⋙ V₁) (σ : K ⋙ U₁ ⟶ U₂ ⋙ H)
    (hσ : (mateEquiv b₁ b₂ (TwoSquare.mk K U₂ U₁ H σ)) = e.hom) :
    (mateEquiv a₁ a₂ (TwoSquare.mk U₁ G F U₂
      ((conjugateIsoEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e).hom)) = σ := by
  have h : mateEquiv a₁ a₂ (TwoSquare.mk U₁ G F U₂
      ((conjugateIsoEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e).hom) =
      TwoSquare.mk K U₂ U₁ H σ := by
    apply (mateEquiv b₁ b₂).injective
    refine NatTrans.ext (funext ?_)
    rw [iterated_mateEquiv_conjugateEquiv, hσ]
    intro X
    change ((conjugateEquiv (a₁.comp b₁) (b₂.comp a₂))
      ((conjugateEquiv (a₁.comp b₁) (b₂.comp a₂)).symm e.hom)).app X = e.hom.app X
    exact congr_app (Equiv.apply_symm_apply _ _) X
  exact h

private theorem isIso_left_mate_of_iterated
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {H : C ⥤ A} {G : B ⥤ D} {K : D ⥤ B}
    (b₁ : F ⊣ H) (b₂ : G ⊣ K) (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    (hτ : IsIso ((mateEquiv b₂ b₁ (TwoSquare.mk _ _ _ _ τ)))) :
    IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ))) := by
  let δ := (mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)
  have hm : mateEquiv a₁ a₂ δ = TwoSquare.mk _ _ _ _ τ := Equiv.apply_symm_apply _ _
  have h := iterated_mateEquiv_conjugateEquiv a₁ a₂ b₁ b₂ δ
  rw [hm] at h
  have : IsIso (conjugateEquiv (a₁.comp b₂) (b₁.comp a₂) δ) := h ▸ hτ
  exact conjugateEquiv_of_iso (a₁.comp b₂) (b₁.comp a₂) δ

private theorem left_mate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂) {F : A ⥤ C} {G : B ⥤ D}
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (P : A) :
    ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P =
      E₂.map (F.map (a₁.unit.app P)) ≫ E₂.map (τ.app (E₁.obj P)) ≫
        a₂.counit.app (G.obj (E₁.obj P)) := by
  simp [mateEquiv]

private noncomputable def homotopySquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (τ : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) :
    F₁.mapHomotopyCategory (.up ℤ) ⋙ F₂.mapHomotopyCategory (.up ℤ) ⟶
      G₁.mapHomotopyCategory (.up ℤ) ⋙ G₂.mapHomotopyCategory (.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl (F₁ ⋙ F₂)) (.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory τ (.up ℤ) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv

private theorem homotopySquare_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    (τ : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) (K : HomotopyCategory A (.up ℤ)) :
    (homotopySquare τ).app K = (NatTrans.mapHomotopyCategory τ (.up ℤ)).app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient _ _).map (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  simp only [homotopySquare, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, hi, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem homotopy_left_mate_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂) {F : A ⥤ C} {G : B ⥤ D}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive] [F.Additive] [G.Additive]
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    [IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)))]
    (P : HomotopyCategory A (.up ℤ)) :
    IsIso (((mateEquiv (a₁.mapHomotopyCategory (.up ℤ))
      (a₂.mapHomotopyCategory (.up ℤ))).symm
        (TwoSquare.mk _ _ _ _ (homotopySquare τ))).app P) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  let δ := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ))
  let q := HomotopyCategory.quotient D (.up ℤ)
  have he : ((mateEquiv (a₁.mapHomotopyCategory (.up ℤ))
      (a₂.mapHomotopyCategory (.up ℤ))).symm
        (TwoSquare.mk _ _ _ _ (homotopySquare τ))).app
          ((HomotopyCategory.quotient _ _).obj P) =
      q.map ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P) := by
    rw [left_mate_app, Adjunction.mapHomotopyCategory_unit_app_quotient]
    erw [Adjunction.mapHomotopyCategory_counit_app_quotient, homotopySquare_app]
    change q.map _ ≫ q.map _ ≫ q.map _ = _
    rw [← q.map_comp, ← q.map_comp]
    congr 1
    ext i
    simp only [δ, left_mate_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      Adjunction.mapHomologicalComplex_unit_app_f,
      Adjunction.mapHomologicalComplex_counit_app_f]
    rfl
  rw [he]
  have : IsIso δ := inferInstance
  have : IsIso ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P) :=
    ((NatIso.mapHomologicalComplex (asIso δ) (.up ℤ)).app P).isIso_hom
  infer_instance

private theorem derived_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : HomotopyCategory A (.up ℤ)) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app P) ≫
      F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((homotopySquare e.hom).app P) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app P) ≫
      G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj P) := by
  have h := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj e P
  apply (cancel_epi
    (F₂.mapDerivedCategoryFactorsh.inv.app ((F₁.mapHomotopyCategory (.up ℤ)).obj P) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.inv.app P))).mp
  simp only [Category.assoc, ← F₂.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact h.symm

private theorem left_mate_normalization
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {E₁ : C₁ ⥤ C₂} {U₁ : C₂ ⥤ C₁} {E₂ : C₃ ⥤ C₄} {U₂ : C₄ ⥤ C₃}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : D₃ ⥤ D₄} {R₂ : D₄ ⥤ D₃}
    (d₁ : L₁ ⊣ R₁) (d₂ : L₂ ⊣ R₂)
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃) (Q₄ : C₄ ⥤ D₄)
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄} {Fd : D₁ ⥤ D₃} {Gd : D₂ ⥤ D₄}
    (α₁ : Q₁ ⋙ L₁ ⟶ E₁ ⋙ Q₂) (α₂ : Q₃ ⋙ L₂ ⟶ E₂ ⋙ Q₄)
    (β₁ : Q₂ ⋙ R₁ ≅ U₁ ⋙ Q₁) (β₂ : Q₄ ⋙ R₂ ≅ U₂ ⋙ Q₃)
    (γ₁ : Q₁ ⋙ Fd ≅ F ⋙ Q₃) (γ₂ : Q₂ ⋙ Gd ≅ G ⋙ Q₄)
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (τd : R₁ ⋙ Fd ⟶ Gd ⋙ R₂)
    (h₁ : ∀ P, d₁.unit.app (Q₁.obj P) ≫ R₁.map (α₁.app P) ≫
      β₁.hom.app (E₁.obj P) = Q₁.map (a₁.unit.app P))
    (h₂ : ∀ P, d₂.unit.app (Q₃.obj P) ≫ R₂.map (α₂.app P) ≫
      β₂.hom.app (E₂.obj P) = Q₃.map (a₂.unit.app P))
    (hτ : ∀ N, Fd.map (β₁.hom.app N) ≫ γ₁.hom.app (U₁.obj N) ≫ Q₃.map (τ.app N) =
      τd.app (Q₂.obj N) ≫ R₂.map (γ₂.hom.app N) ≫ β₂.hom.app (G.obj N)) (P : C₁) :
    ((mateEquiv d₁ d₂).symm (TwoSquare.mk _ _ _ _ τd)).app (Q₁.obj P) ≫
      Gd.map (α₁.app P) ≫ γ₂.hom.app (E₁.obj P) =
    L₂.map (γ₁.hom.app P) ≫ α₂.app (F.obj P) ≫
      Q₄.map (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P) := by
  apply (d₂.homEquiv _ _).injective
  apply (cancel_mono (β₂.hom.app (G.obj (E₁.obj P)))).mp
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (unit_mateEquiv_symm d₁ d₂ (TwoSquare.mk _ _ _ _ τd) (Q₁.obj P))]
  rw [← reassoc_of% τd.naturality (α₁.app P)]
  rw [← hτ (E₁.obj P)]
  rw [← Fd.map_comp_assoc, ← Fd.map_comp_assoc, Category.assoc, h₁]
  rw [reassoc_of% γ₁.hom.naturality (a₁.unit.app P)]
  rw [← Q₃.map_comp]
  have hu : F.map (a₁.unit.app P) ≫ τ.app (E₁.obj P) =
      a₂.unit.app (F.obj P) ≫ U₂.map
        (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P) :=
    unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ τ) P
  rw [hu]
  rw [Q₃.map_comp]
  have hb := β₂.hom.naturality
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hb
  rw [hb]
  rw [← reassoc_of% d₂.unit.naturality (γ₁.hom.app P)]
  rw [← reassoc_of% (h₂ (F.obj P))]

private theorem localized_mate_isIso_at
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    {E₁ : C₁ ⥤ C₂} {U₁ : C₂ ⥤ C₁} {E₂ : C₃ ⥤ C₄} {U₂ : C₄ ⥤ C₃}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : D₁ ⥤ D₂} {R₁ : D₂ ⥤ D₁} {L₂ : D₃ ⥤ D₄} {R₂ : D₄ ⥤ D₃}
    (d₁ : L₁ ⊣ R₁) (d₂ : L₂ ⊣ R₂)
    (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃) (Q₄ : C₄ ⥤ D₄)
    {F : C₁ ⥤ C₃} {G : C₂ ⥤ C₄} {Fd : D₁ ⥤ D₃} {Gd : D₂ ⥤ D₄}
    (α₁ : Q₁ ⋙ L₁ ⟶ E₁ ⋙ Q₂) (α₂ : Q₃ ⋙ L₂ ⟶ E₂ ⋙ Q₄)
    (β₁ : Q₂ ⋙ R₁ ≅ U₁ ⋙ Q₁) (β₂ : Q₄ ⋙ R₂ ≅ U₂ ⋙ Q₃)
    (γ₁ : Q₁ ⋙ Fd ≅ F ⋙ Q₃) (γ₂ : Q₂ ⋙ Gd ≅ G ⋙ Q₄)
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (τd : R₁ ⋙ Fd ⟶ Gd ⋙ R₂)
    (h₁ : ∀ P, d₁.unit.app (Q₁.obj P) ≫ R₁.map (α₁.app P) ≫
      β₁.hom.app (E₁.obj P) = Q₁.map (a₁.unit.app P))
    (h₂ : ∀ P, d₂.unit.app (Q₃.obj P) ≫ R₂.map (α₂.app P) ≫
      β₂.hom.app (E₂.obj P) = Q₃.map (a₂.unit.app P))
    (hτ : ∀ N, Fd.map (β₁.hom.app N) ≫ γ₁.hom.app (U₁.obj N) ≫ Q₃.map (τ.app N) =
      τd.app (Q₂.obj N) ≫ R₂.map (γ₂.hom.app N) ≫ β₂.hom.app (G.obj N)) (P : C₁)
    [IsIso (α₁.app P)] [IsIso (α₂.app (F.obj P))]
    [IsIso (((mateEquiv (G := F) (H := G) a₁ a₂).symm
      (TwoSquare.mk U₁ G F U₂ τ)).app P)] :
    IsIso (((mateEquiv (G := Fd) (H := Gd) d₁ d₂).symm
      (TwoSquare.mk R₁ Gd Fd R₂ τd)).app (Q₁.obj P)) := by
  have h := left_mate_normalization (F := F) (G := G) (Fd := Fd) (Gd := Gd)
    a₁ a₂ d₁ d₂ Q₁ Q₂ Q₃ Q₄ α₁ α₂ β₁ β₂ γ₁ γ₂ τ τd h₁ h₂ hτ P
  have hi : IsIso (((mateEquiv (G := Fd) (H := Gd) d₁ d₂).symm
      (TwoSquare.mk R₁ Gd Fd R₂ τd)).app (Q₁.obj P) ≫
      Gd.map (α₁.app P) ≫ γ₂.hom.app (E₁.obj P)) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_right_iff] using hi

private theorem isIso_left_mate_change_adjunction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ E₁ : A ⥤ B} {U₁ : B ⥤ A} {L₂ E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (d₁ : L₁ ⊣ U₁) (d₂ : L₂ ⊣ U₂) (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {G : B ⥤ D} (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    [IsIso (((mateEquiv (G := F) (H := G) a₁ a₂).symm (TwoSquare.mk U₁ G F U₂ τ)))] :
    IsIso (((mateEquiv (G := F) (H := G) d₁ d₂).symm (TwoSquare.mk U₁ G F U₂ τ))) := by
  let e₁ : L₁ ≅ E₁ := Adjunction.leftAdjointUniq d₁ a₁
  let e₂ : L₂ ≅ E₂ := Adjunction.leftAdjointUniq d₂ a₂
  apply (NatTrans.isIso_iff_isIso_app
    (((mateEquiv (G := F) (H := G) d₁ d₂).symm (TwoSquare.mk U₁ G F U₂ τ)))).2
  intro P
  have h := left_mate_normalization (F := F) (G := G) (Fd := F) (Gd := G) a₁ a₂ d₁ d₂
    (𝟭 A) (𝟭 B) (𝟭 C) (𝟭 D) e₁.hom e₂.hom
    (Iso.refl U₁) (Iso.refl U₂) (Iso.refl F) (Iso.refl G) τ τ
    (fun P ↦ by
      change d₁.unit.app P ≫ U₁.map (e₁.hom.app P) ≫ 𝟙 _ = a₁.unit.app P
      rw [Category.comp_id]
      exact Adjunction.unit_leftAdjointUniq_hom_app d₁ a₁ P)
    (fun P ↦ by
      change d₂.unit.app P ≫ U₂.map (e₂.hom.app P) ≫ 𝟙 _ = a₂.unit.app P
      rw [Category.comp_id]
      exact Adjunction.unit_leftAdjointUniq_hom_app d₂ a₂ P)
    (fun N ↦ by simp) P
  change ((mateEquiv (G := F) (H := G) d₁ d₂).symm (TwoSquare.mk U₁ G F U₂ τ)).app P ≫
    G.map (e₁.hom.app P) ≫ 𝟙 _ =
      L₂.map (𝟙 _) ≫ e₂.hom.app (F.obj P) ≫
      ((mateEquiv (G := F) (H := G) a₁ a₂).symm (TwoSquare.mk U₁ G F U₂ τ)).app P at h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at h
  have hi : IsIso (((mateEquiv (G := F) (H := G) d₁ d₂).symm
      (TwoSquare.mk U₁ G F U₂ τ)).app P ≫
      G.map (e₁.hom.app P)) := by
    rw [h]
    have : IsIso (((mateEquiv (G := F) (H := G) a₁ a₂).symm
        (TwoSquare.mk U₁ G F U₂ τ)).app P) :=
      NatIso.isIso_app_of_isIso
        (((mateEquiv (G := F) (H := G) a₁ a₂).symm (TwoSquare.mk U₁ G F U₂ τ))) P
    have : IsIso (e₂.hom.app (F.obj P)) := (e₂.app (F.obj P)).isIso_hom
    infer_instance
  have : IsIso (G.map (e₁.hom.app P)) := (G.mapIso (e₁.app P)).isIso_hom
  exact (isIso_comp_right_iff
    (((mateEquiv (G := F) (H := G) d₁ d₂).symm (TwoSquare.mk U₁ G F U₂ τ)).app P)
    (G.map (e₁.hom.app P))).1 hi

private theorem derived_square_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso e).inv =
      (Functor.mapDerivedCategorySquareIso e.symm).hom := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private theorem derived_square_normalization_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : HomotopyCategory A (.up ℤ)) :
    G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactorsh.hom.app P) ≫
      G₂.mapDerivedCategoryFactorsh.hom.app ((G₁.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((homotopySquare e.inv).app P) =
    (Functor.mapDerivedCategorySquareIso e).inv.app (DerivedCategory.Qh.obj P) ≫
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactorsh.hom.app P) ≫
      F₂.mapDerivedCategoryFactorsh.hom.app ((F₁.mapHomotopyCategory (.up ℤ)).obj P) := by
  rw [derived_square_inv]
  exact derived_square_normalization e.symm P

-- The kernel need not be finitely generated: each local tensor lift is a finite sum.
private theorem flat_local_relations {R : Type (u + 1)} [CommRing R]
    {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
    [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]
    {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) :
    Presheaf.HasLocallyTrivialRelations J F.obj := by
  classical
  intro V s q y e he
  let φ := e.mulVecLin
  let N := LinearMap.ker φ
  let S₀ := ShortComplex.moduleCatMkOfKerLERange
    (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom φ) (by simp [N])
  have hS₀ : S₀.Exact := ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ (by simp [N])
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft F) := hF.tensorLeft.1
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft F) := hF.tensorLeft.2
  let Φ : ModuleCat.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
    Functor.const Dᵒᵖ ⋙ MonoidalCategory.tensorLeft F.obj ⋙ presheafToSheaf J _
  let eΦ : constantSheaf J (ModuleCat.{u + 1} R) ⋙ MonoidalCategory.tensorLeft F ≅ Φ :=
    Functor.isoWhiskerLeft _ ((MonoidalCategory.curriedTensor _).mapIso
      (asIso ((sheafificationAdjunction J _).counit.app F)).symm) ≪≫
      Functor.isoWhiskerLeft (Functor.const Dᵒᵖ)
        (Sheaf.presheafToSheafCompTensorLeftIso F.obj)
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteColimits _ _
  have hS : (S₀.map Φ).Exact :=
    (ShortComplex.exact_iff_of_iso (S₀.mapNatIso eΦ)).1
      ((hS₀.map (constantSheaf J _)).map (MonoidalCategory.tensorLeft F))
  let Sp := S₀.map (Functor.const Dᵒᵖ ⋙ MonoidalCategory.tensorLeft F.obj)
  let x : Sp.X₂.obj (Opposite.op V) :=
    ∑ j, y j ⊗ₜ[R] (Pi.single j 1 : Fin s → R)
  have hx : Sp.g.app (Opposite.op V) x = 0 := by
    refine (TensorProduct.piScalarRight R R _ (Fin q)).injective ?_
    ext l
    change TensorProduct.piScalarRight R R _ (Fin q) (φ.lTensor _ x) l = 0
    rw [TensorProduct.piScalarRight_lTensor_mulVecLin,
      TensorProduct.piScalarRight_sum_tmul_single]
    exact he l
  refine ⟨_, Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf hS x hx, ?_⟩
  rintro W f ⟨z₀, hz₀⟩
  obtain ⟨t, z, b, hz⟩ := TensorProduct.exists_sum_tmul_eq z₀
  refine ⟨t, fun j m ↦ (b m).val j, z, ?_, ?_⟩
  · ext l m
    have hb : φ (b m).val = 0 := (b m).property
    simpa only [φ, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Pi.zero_apply, Matrix.mul_apply, Matrix.zero_apply] using congrFun hb l
  · intro j
    have hy := congrArg (fun w ↦ TensorProduct.piScalarRight R R _ (Fin s) w j) hz₀
    change TensorProduct.piScalarRight R R _ (Fin s) (N.subtype.lTensor _ z₀) j =
      TensorProduct.piScalarRight R R _ (Fin s)
        (TensorProduct.map (F.obj.map f.op).hom LinearMap.id x) j at hy
    rw [hz] at hy
    simpa [x, map_sum, Finset.sum_smul, Pi.single_apply] using hy.symm

private theorem local_relations_lan
    {C₀ D₀ : Type (u + 1)} [Category.{u} C₀] [Category.{u} D₀]
    [EssentiallySmall.{u + 1} C₀] {J₀ : GrothendieckTopology C₀}
    {K₀ : GrothendieckTopology D₀} {R₀ : Type (u + 1)} [CommRing R₀]
    {G : C₀ ⥤ D₀} [RepresentablyFlat G]
    [∀ P : C₀ᵒᵖ ⥤ ModuleCat.{u + 1} R₀, G.op.HasPointwiseLeftKanExtension P]
    (hG : CoverPreserving J₀ K₀ G) {F₀ : C₀ᵒᵖ ⥤ ModuleCat.{u + 1} R₀}
    (hF : Presheaf.HasLocallyTrivialRelations J₀ F₀) :
    Presheaf.HasLocallyTrivialRelations K₀ (G.op.lan.obj F₀) := by
  intro U s q y e hey
  let P := G.op.lan.obj F₀
  -- the elements `yⱼ` and their relations come from one stage `F(V)` of the colimit
  have : IsFiltered (CostructuredArrow G.op (op U)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G U)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{u + 1} R₀)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let hcol := G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F₀ (op U)
  obtain ⟨T₀, y', hy', hey'⟩ := ModuleCat.exists_lift_of_isColimit hcol y e hey
  -- the relations are trivial locally on `V`, as `F` is flat
  obtain ⟨S, hS, hfac⟩ :=
    hF (V := T₀.left.unop) y' e hey'
  refine ⟨_, K₀.pullback_stable T₀.hom.unop (hG.cover_preserve hS), ?_⟩
  rintro U' h ⟨W, f, h', hf, hcomp⟩
  obtain ⟨t', b, z, heb, hyz⟩ := hfac f hf
  -- restricted to `U'`, each `yⱼ` is `∑ₘ bⱼₘ wₘ`
  refine ⟨t', b, fun m ↦ P.map h'.op ((G.op.leftKanExtensionUnit F₀).app (op W) (z m)),
    heb, fun j ↦ ?_⟩
  rw [← hy' j]
  change P.map h.op (P.map T₀.hom ((G.op.leftKanExtensionUnit F₀).app T₀.left (y' j))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have hτ : T₀.hom ≫ h.op = G.op.map f.op ≫ h'.op :=
    Quiver.Hom.unop_inj (by simpa using hcomp)
  rw [hτ, Functor.map_comp, ConcreteCategory.comp_apply]
  have hnat := NatTrans.naturality_apply (G.op.leftKanExtensionUnit F₀) f.op (y' j)
  change _ = P.map (G.op.map f.op) _ at hnat
  rw [← hnat, hyz j]
  simp only [map_sum, map_smul]
  rfl

private theorem flat_pullback_of_local_relations
    {C₀ D₀ : Type (u + 1)} [Category.{u} C₀] [Category.{u} D₀]
    [EssentiallySmall.{u + 1} C₀] [EssentiallySmall.{u + 1} D₀]
    {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
    {R₀ : Type (u + 1)} [CommRing R₀]
    [J₀.HasSheafCompose (forget (ModuleCat.{u + 1} R₀))]
    [J₀.WEqualsLocallyBijective (ModuleCat.{u + 1} R₀)]
    [K₀.HasSheafCompose (forget (ModuleCat.{u + 1} R₀))]
    [K₀.WEqualsLocallyBijective (ModuleCat.{u + 1} R₀)]
    {G : C₀ ⥤ D₀} [RepresentablyFlat G]
    [∀ P : C₀ᵒᵖ ⥤ ModuleCat.{u + 1} R₀, G.op.HasPointwiseLeftKanExtension P]
    (hG : CoverPreserving J₀ K₀ G) {F : Sheaf J₀ (ModuleCat.{u + 1} R₀)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat
      ((Functor.sheafPullbackConstruction.sheafPullback G
        (ModuleCat.{u + 1} R₀) J₀ K₀).obj F) :=
  Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
    (local_relations_lan hG (flat_local_relations hF))

private theorem derived_mate_isIso_of_flat
    {A B C D : Type*} [Category.{v₁} A] [Category B] [Category.{v₂} C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution C]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [E₂.Additive] [U₁.Additive] [U₂.Additive]
    [E₁.PreservesKFlatQuasiIso] [E₂.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    (d₁ : DerivedAdjunctionWithUnit a₁) (d₂ : DerivedAdjunctionWithUnit a₂)
    (F : A ⥤ C) (G : B ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F.PreservesFlat] [PreservesColimitsOfShape ℤ F]
    (e : G ⋙ U₂ ≅ U₁ ⋙ F)
    [IsIso (((mateEquiv (G := F) (H := G) a₁ a₂).symm
      (TwoSquare.mk _ _ _ _ e.inv)))] :
    IsIso (((mateEquiv (G := F.mapDerivedCategory) (H := G.mapDerivedCategory)
      d₁.adjunction d₂.adjunction).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv))) := by
  let δ : F.mapDerivedCategory ⋙ E₂.leftDerivedFunctor ⟶
      E₁.leftDerivedFunctor ⋙ G.mapDerivedCategory :=
    ((mateEquiv (G := F.mapDerivedCategory) (H := G.mapDerivedCategory)
      d₁.adjunction d₂.adjunction).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv))
  have hgood (P : HomotopyCategory A
      (.up ℤ)) (hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P)
      (hFP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
        ((F.mapHomotopyCategory (.up ℤ)).obj P)) :
      IsIso (δ.app (DerivedCategory.Qh.obj P)) := by
    have : IsIso (E₁.leftDerivedFunctorCounit.app P) :=
      E₁.derives_kFlat.isIso_of_isLeftDerivedFunctor (LF := E₁.leftDerivedFunctor)
      E₁.leftDerivedFunctorCounit ⟨P, hP⟩
    have : IsIso (E₂.leftDerivedFunctorCounit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
      E₂.derives_kFlat.isIso_of_isLeftDerivedFunctor (LF := E₂.leftDerivedFunctor)
      E₂.leftDerivedFunctorCounit ⟨(F.mapHomotopyCategory (.up ℤ)).obj P, hFP⟩
    have := homotopy_left_mate_isIso (F := F) (G := G)
      a₁
      a₂
      e.inv P
    exact localized_mate_isIso_at
      (F := F.mapHomotopyCategory (.up ℤ)) (G := G.mapHomotopyCategory (.up ℤ))
      (Fd := F.mapDerivedCategory) (Gd := G.mapDerivedCategory)
      (a₁.mapHomotopyCategory (.up ℤ))
      (a₂.mapHomotopyCategory (.up ℤ))
      d₁.adjunction
      d₂.adjunction
      DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
      E₁.leftDerivedFunctorCounit E₂.leftDerivedFunctorCounit
      U₁.mapDerivedCategoryFactorsh U₂.mapDerivedCategoryFactorsh
      F.mapDerivedCategoryFactorsh G.mapDerivedCategoryFactorsh
      (homotopySquare (F₁ := U₁) (F₂ := F) (G₁ := G) (G₂ := U₂)
        e.inv)
      (Functor.mapDerivedCategorySquareIso e).inv
      d₁.unit_formula
      d₂.unit_formula
      (derived_square_normalization_inv e) P
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro X
  obtain ⟨M, hM, hFM, ⟨eM⟩⟩ := exists_comparison_kFlat_representative F X
  exact (NatTrans.isIso_app_iff_of_iso δ eM).1 (hgood M hM hFM)

-- Elaborate the shared site instances sequentially.
set_option Elab.async false

/-- The positive quotient at exponent n+1, as a discrete coefficient type. -/
def PbcQuotient {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  A ⧸ d.ideal ^ (n + 1)

/-- The actual quotient ring structure. -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    CommRing (PbcQuotient d n) := inferInstanceAs (CommRing (A ⧸ d.ideal ^ (n + 1)))

/-- Finiteness of the quotient coefficient set. -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    Finite (PbcQuotient d n) := d.quotientFinite n

/-- Each quotient coefficient ring has the discrete topology. -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    TopologicalSpace (PbcQuotient d n) := ⊥

/-- Discreteness of the quotient topology. -/
instance {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    DiscreteTopology (PbcQuotient d n) := ⟨rfl⟩

/-- The canonical quotient homomorphism at positive coefficient levels. -/
noncomputable def pbcWitnessQuotientMap {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (b a : ℕ) (h : a ≤ b) :
    PbcQuotient d b →+* PbcQuotient d a :=
  Scheme.adicQuotientMap d.ideal (b + 1) (a + 1) (Nat.add_le_add_right h 1)

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

private instance sheaf_countableCoproducts (R : Type (u + 1)) [CommRing R] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
  haveI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  haveI : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩

private noncomputable def scalarExtension {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

private noncomputable def scalarAdjunction {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    scalarExtension J φ ⊣ Sheaf.restrictScalars J φ :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private instance restriction_preservesFiniteLimits {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteLimits (Sheaf.restrictScalars J φ) := by
  have : PreservesLimitsOfSize.{0, 0} (Sheaf.restrictScalars J φ) :=
    (scalarAdjunction J φ).rightAdjoint_preservesLimits
  infer_instance

private instance restriction_preservesFiniteColimits {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteColimits (Sheaf.restrictScalars J φ) := by
  have : PreservesColimitsOfSize.{0, 0} (Sheaf.restrictScalars J φ) :=
    (Sheaf.restrictCoextendScalarsAdj J φ).leftAdjoint_preservesColimits
  infer_instance

private instance scalarExtension_additive {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) : (scalarExtension J φ).Additive :=
  (scalarAdjunction J φ).left_adjoint_additive

private instance scalarExtension_preservesKFlat {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (scalarExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := scalarExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  infer_instance

private noncomputable def scalarDerivedAdjunctionData {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :=
  normalizedDerivedAdjunction
    (A := Sheaf J (ModuleCat.{u + 1} R)) (B := Sheaf J (ModuleCat.{u + 1} S))
    (E := scalarExtension J φ) (U := Sheaf.restrictScalars J φ)
    (scalarAdjunction J φ)

attribute [local irreducible] scalarDerivedAdjunctionData

private noncomputable def scalarDerivedAdjunction {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (scalarExtension J φ).leftDerivedFunctor ⊣ Sheaf.derivedRestrictScalars J φ :=
  (scalarDerivedAdjunctionData J φ).adjunction

-- Keep the scalar adjunction data folded when elaborating the chosen left adjoints.
attribute [local irreducible] scalarDerivedAdjunction scalarExtension scalarAdjunction

/-- Derived restriction of scalars has a left adjoint for an arbitrary coefficient map. -/
@[instance] theorem pbcRestriction_isRightAdjoint {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.derivedRestrictScalars J φ).IsRightAdjoint := by
  exact (scalarDerivedAdjunction J φ).isRightAdjoint

/-- Derived scalar extension, fixed by the adjunction to actual restriction of scalars. -/
noncomputable def pbcFixedScalarExtension {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)) :=
  (Sheaf.derivedRestrictScalars J φ).leftAdjoint

/-- The canonical composition comparison of derived scalar extensions, obtained by
conjugating the actual composition identification for restrictions of scalars. -/
noncomputable def pbcFixedScalarExtensionComp {R S V : Type (u + 1)}
    [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    pbcFixedScalarExtension J φ ⋙ pbcFixedScalarExtension J ψ ≅ pbcFixedScalarExtension J χ :=
  Adjunction.leftAdjointCompIso
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J χ))
    (Sheaf.derivedRestrictScalarsCompIso J h)

variable (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]

private instance comparison_integerColimits (R : Type (u + 1)) [CommRing R] :
    PreservesColimitsOfShape ℤ (comparisonUpperStar (ModuleCat.{u + 1} R) T) := by
  have : PreservesColimitsOfSize.{0, 0} (comparisonUpperStar (ModuleCat.{u + 1} R) T) :=
    (comparisonAdjunction (ModuleCat.{u + 1} R) T).leftAdjoint_preservesColimits
  infer_instance

/-- Restriction commutes with comparison inverse image. This is the conjugate of the
sectionwise commutation of comparison restriction with coextension of scalars. -/
noncomputable def pbcComparisonRestrict (φ : R →+* S) :
    comparisonUpperStar (ModuleCat.{u + 1} S) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T :=
  ((conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} S) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ).comp
      (comparisonAdjunction (ModuleCat.{u + 1} R) T))).symm (Iso.refl _)).symm

/-- Exact descent of the preceding canonical restriction comparison. -/
noncomputable def pbcDerivedComparisonRestrict (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} S) T)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := comparisonUpperStar (ModuleCat.{u + 1} S) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
      (G := Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
        comparisonUpperStar (ModuleCat.{u + 1} R) T)
      (pbcComparisonRestrict T φ) ≪≫
      (Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (comparisonUpperStar (ModuleCat.{u + 1} R) T)).symm

/-- The canonical scalar-extension comparison is the mate of the restriction comparison. -/
noncomputable def pbcComparisonReductionMap (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ⟶
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  ((mateEquiv
    (G := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
    (H := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv))

private theorem comparison_preservesFlat (R : Type (u + 1)) [CommRing R] :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).PreservesFlat :=
  ⟨fun hF ↦ flat_pullback_of_local_relations (G := Scheme.toProEt T)
      (coverPreserving_toProEt T) hF⟩

-- Restricting the site commutes with the pointwise coextension adjunction.
private theorem restrict_coextend_mate (φ : R →+* S) :
    (mateEquiv
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
      (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ)
      (TwoSquare.mk _ _ _ _
        (show comparisonLowerStar (ModuleCat.{u + 1} S) T ⋙
            Sheaf.restrictScalars T.smallEtaleTopology φ ⟶
          Sheaf.restrictScalars (Scheme.ProEt.topology T) φ ⋙
            comparisonLowerStar (ModuleCat.{u + 1} R) T from 𝟙 _))) = 𝟙 _ := by
  ext F V x
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.id_comp]
  change (((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app
      ((ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).obj
        (F.obj.obj ((Scheme.toProEt T).op.obj V)))) ≫
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).map
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).counit.app
          (F.obj.obj ((Scheme.toProEt T).op.obj V)))).hom x = x
  exact congrArg (fun f ↦ f.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components _)

private theorem comparison_restrict_mate (φ : R →+* S) :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} S) T)
      (comparisonAdjunction (ModuleCat.{u + 1} R) T)
      (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv)) = 𝟙 _ := by
  exact mate_of_conjugate
    (comparisonAdjunction (ModuleCat.{u + 1} S) T)
    (comparisonAdjunction (ModuleCat.{u + 1} R) T)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
    (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ)
    (Iso.refl _) (𝟙 _) (restrict_coextend_mate T φ)

private theorem ordinary_scalar_mate_isIso (φ : R →+* S) :
    IsIso (((mateEquiv (scalarAdjunction T.smallEtaleTopology φ)
      (scalarAdjunction (Scheme.ProEt.topology T) φ)).symm
      (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv))) := by
  apply isIso_left_mate_of_iterated
    (scalarAdjunction T.smallEtaleTopology φ)
    (scalarAdjunction (Scheme.ProEt.topology T) φ)
    (comparisonAdjunction (ModuleCat.{u + 1} R) T)
    (comparisonAdjunction (ModuleCat.{u + 1} S) T)
  rw [comparison_restrict_mate]
  infer_instance

attribute [local irreducible] pbcComparisonRestrict

private theorem computed_comparison_mate_isIso (φ : R →+* S) :
    IsIso (((mateEquiv
      (G := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
      (H := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
      (scalarDerivedAdjunctionData T.smallEtaleTopology φ).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) φ).adjunction).symm
      (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv))) := by
  have := comparison_preservesFlat T R
  have := ordinary_scalar_mate_isIso T φ
  exact derived_mate_isIso_of_flat
    (A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (B := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (D := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (E₁ := scalarExtension T.smallEtaleTopology φ)
    (E₂ := scalarExtension (Scheme.ProEt.topology T) φ)
    (U₁ := Sheaf.restrictScalars T.smallEtaleTopology φ)
    (U₂ := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
    (scalarAdjunction T.smallEtaleTopology φ)
    (scalarAdjunction (Scheme.ProEt.topology T) φ)
    (scalarDerivedAdjunctionData T.smallEtaleTopology φ)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) φ)
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
    (comparisonUpperStar (ModuleCat.{u + 1} S) T)
    (pbcComparisonRestrict T φ)

/-- The canonical mate is invertible, with no flatness condition on the ring map. -/
theorem pbcComparisonReductionMap_isIso (φ : R →+* S) :
    IsIso (pbcComparisonReductionMap T φ) := by
  have := computed_comparison_mate_isIso T φ
  exact isIso_left_mate_change_adjunction
    (F := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
    (G := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))
    (scalarDerivedAdjunctionData T.smallEtaleTopology φ).adjunction
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) φ).adjunction
    (pbcDerivedComparisonRestrict T φ).inv

/-- The source identification in the witness compatibility equation. -/
noncomputable def pbcComparisonReduction (φ : R →+* S) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology T) φ ≅
      pbcFixedScalarExtension T.smallEtaleTopology φ ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory :=
  haveI := pbcComparisonReductionMap_isIso T φ
  asIso (pbcComparisonReductionMap T φ)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {A : Type (u + 1)} [CommRing A]

/-- Ambient finite-level pro-étale derived objects, in the canonical fixed-ring
presentation. -/
abbrev PbcWitnessAmbient (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (PbcQuotient d n)))

/-- Ambient finite-level étale derived objects. -/
abbrev PbcWitnessEtale (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :=
  DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (PbcQuotient d n)))

/-- Coefficient reduction between consecutive ambient pro-étale levels. -/
noncomputable def pbcWitnessReduction (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessAmbient T d (n + 1) ⥤ PbcWitnessAmbient T d n :=
  pbcFixedScalarExtension (Scheme.ProEt.topology T)
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))

/-- Coefficient reduction between consecutive ambient étale levels. -/
noncomputable def pbcWitnessEtaleReduction
    (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    PbcWitnessEtale T d (n + 1) ⥤ PbcWitnessEtale T d n :=
  pbcFixedScalarExtension T.smallEtaleTopology (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))

/-- The bounded constructible input property, transported by the recorded canonical
coefficient realization. -/
def pbcWitnessBoundedConstructible (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    ObjectProperty (PbcWitnessAmbient T d n) :=
  fun K ↦ isBoundedConstructibleFiniteCoefficient T (PbcQuotient d n)
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj K)

/-- Reflect the retained origin isomorphism through the canonical realization. This
uses the retained-pair definition without defining another notion of origin. -/
noncomputable def pbcFixedOriginAlpha (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus
      ((finiteCoefficientRealization T Λ).mapDerivedCategory.obj K))
    (W : EtaleOriginWitness T Λ
      ⟨(finiteCoefficientRealization T Λ).mapDerivedCategory.obj K, hK⟩) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj W.L.obj ≅ K :=
  (finiteCoefficientRealization T Λ).mapDerivedCategory.preimageIso
    ((Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
      (finiteCoefficientRealization T Λ)).app W.L.obj ≪≫
        DerivedCategory.Plus.ι.mapIso W.alpha)

/-- A normalized tower with compatible retained origins: ambient pro-étale levels with
étale origins and compatible normalization isomorphisms between adjacent levels. -/
structure PbcWitnessedTower (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) where
  /-- The ambient pro-étale levels. -/
  K : ∀ n : ℕ, PbcWitnessAmbient T d n
  /-- Each level is bounded below. -/
  boundedBelow : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n))
  /-- The retained pairs are those of the supplied étale-origin interface. -/
  origin : ∀ n : ℕ, EtaleOriginWitness T (PbcQuotient d n)
    ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (K n),
      boundedBelow n⟩
  /-- Input or output normalization at adjacent quotients. -/
  theta : ∀ n : ℕ, (pbcWitnessReduction T d n).obj (K (n + 1)) ≅ K n
  /-- Normalization on the retained étale origins. -/
  beta : ∀ n : ℕ,
    (pbcWitnessEtaleReduction T d n).obj (origin (n + 1)).L.obj ≅ (origin n).L.obj
  /-- The source of the right hand side is identified by the canonical tensor mate. -/
  compatibility : ∀ n : ℕ,
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (beta n).hom ≫
          (pbcFixedOriginAlpha T (PbcQuotient d n) (K n) (boundedBelow n) (origin n)).hom =
      (pbcComparisonReduction T (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
          (origin (n + 1)).L.obj ≫
        (pbcWitnessReduction T d n).map (pbcFixedOriginAlpha T (PbcQuotient d (n + 1)) (K (n + 1))
          (boundedBelow (n + 1)) (origin (n + 1))).hom ≫ (theta n).hom

/-- The comparison isomorphism of a retained origin, in the fixed-ring presentation. -/
noncomputable def PbcWitnessedTower.alpha {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.obj
      (P.origin n).L.obj ≅ P.K n :=
  pbcFixedOriginAlpha T (PbcQuotient d n) (P.K n) (P.boundedBelow n) (P.origin n)

/-- A morphism retains both levelwise maps and both normalization compatibilities. -/
@[ext] structure PbcWitnessedTowerHom {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P Q : PbcWitnessedTower T d) where
  /-- The underlying ambient maps. -/
  u : ∀ n : ℕ, P.K n ⟶ Q.K n
  /-- The maps on the retained étale origins. -/
  v : ∀ n : ℕ, (P.origin n).L.obj ⟶ (Q.origin n).L.obj
  /-- Compatibility with pro-étale normalizations. -/
  theta_naturality : ∀ n : ℕ,
    (pbcWitnessReduction T d n).map (u (n + 1)) ≫ (Q.theta n).hom =
      (P.theta n).hom ≫ u n
  /-- Compatibility with étale normalizations. -/
  beta_naturality : ∀ n : ℕ,
    (pbcWitnessEtaleReduction T d n).map (v (n + 1)) ≫ (Q.beta n).hom =
      (P.beta n).hom ≫ v n
  /-- The square involving the two retained comparison isomorphisms commutes. -/
  origin_naturality : ∀ n : ℕ,
    (P.alpha n).hom ≫ u n =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (v n) ≫ (Q.alpha n).hom

/-- Identity pairs satisfy the normalization and origin squares. -/
theorem pbcWitnessedTower_id_laws {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) :
    (∀ n : ℕ, (pbcWitnessReduction T d n).map (𝟙 (P.K (n + 1))) ≫ (P.theta n).hom =
      (P.theta n).hom ≫ 𝟙 (P.K n)) ∧
    (∀ n : ℕ, (pbcWitnessEtaleReduction T d n).map (𝟙 (P.origin (n + 1)).L.obj) ≫
      (P.beta n).hom = (P.beta n).hom ≫ 𝟙 (P.origin n).L.obj) ∧
    (∀ n : ℕ, (P.alpha n).hom ≫ 𝟙 (P.K n) =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (𝟙 (P.origin n).L.obj) ≫ (P.alpha n).hom) := by
  constructor
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  constructor
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · intro n
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The identity has the actual identity map at both kinds of levels. -/
noncomputable def pbcWitnessedTowerId {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    (P : PbcWitnessedTower T d) : PbcWitnessedTowerHom P P where
  u := fun _ ↦ 𝟙 _
  v := fun _ ↦ 𝟙 _
  theta_naturality := (pbcWitnessedTower_id_laws P).1
  beta_naturality := (pbcWitnessedTower_id_laws P).2.1
  origin_naturality := (pbcWitnessedTower_id_laws P).2.2

/-- Composite pairs satisfy the normalization and origin squares. -/
theorem pbcWitnessedTower_comp_laws {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    {P Q V : PbcWitnessedTower T d} (f : PbcWitnessedTowerHom P Q)
    (g : PbcWitnessedTowerHom Q V) :
    (∀ n : ℕ, (pbcWitnessReduction T d n).map (f.u (n + 1) ≫ g.u (n + 1)) ≫
      (V.theta n).hom = (P.theta n).hom ≫ (f.u n ≫ g.u n)) ∧
    (∀ n : ℕ, (pbcWitnessEtaleReduction T d n).map (f.v (n + 1) ≫ g.v (n + 1)) ≫
      (V.beta n).hom = (P.beta n).hom ≫ (f.v n ≫ g.v n)) ∧
    (∀ n : ℕ, (P.alpha n).hom ≫ (f.u n ≫ g.u n) =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        (f.v n ≫ g.v n) ≫ (V.alpha n).hom) := by
  constructor
  · intro n
    rw [Functor.map_comp, Category.assoc, g.theta_naturality,
      ← Category.assoc, f.theta_naturality, Category.assoc]
  constructor
  · intro n
    rw [Functor.map_comp, Category.assoc, g.beta_naturality,
      ← Category.assoc, f.beta_naturality, Category.assoc]
  · intro n
    rw [← Category.assoc, f.origin_naturality, Category.assoc,
      g.origin_naturality, ← Category.assoc, ← Functor.map_comp]

/-- Composition has the actual levelwise composites of both maps. -/
noncomputable def pbcWitnessedTowerComp {T : Scheme.{u}} {d : Scheme.AdicCoefficientDatum A}
    {P Q V : PbcWitnessedTower T d} (f : PbcWitnessedTowerHom P Q)
    (g : PbcWitnessedTowerHom Q V) : PbcWitnessedTowerHom P V where
  u := fun n ↦ f.u n ≫ g.u n
  v := fun n ↦ f.v n ≫ g.v n
  theta_naturality := (pbcWitnessedTower_comp_laws f g).1
  beta_naturality := (pbcWitnessedTower_comp_laws f g).2.1
  origin_naturality := (pbcWitnessedTower_comp_laws f g).2.2

/-- The specified identity and composition satisfy the category axioms. -/
theorem pbcWitnessedTower_category_laws (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) :
    (∀ (P Q : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q),
      pbcWitnessedTowerComp (pbcWitnessedTowerId P) f = f) ∧
    (∀ (P Q : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q),
      pbcWitnessedTowerComp f (pbcWitnessedTowerId Q) = f) ∧
    (∀ (P Q V W : PbcWitnessedTower T d) (f : PbcWitnessedTowerHom P Q)
      (g : PbcWitnessedTowerHom Q V) (h : PbcWitnessedTowerHom V W),
      pbcWitnessedTowerComp (pbcWitnessedTowerComp f g) h =
        pbcWitnessedTowerComp f (pbcWitnessedTowerComp g h)) := by
  constructor
  · intro P Q f
    ext n <;> simp [pbcWitnessedTowerComp, pbcWitnessedTowerId]
  constructor
  · intro P Q f
    ext n <;> simp [pbcWitnessedTowerComp, pbcWitnessedTowerId]
  · intro P Q V W f g h
    ext n <;> simp [pbcWitnessedTowerComp, Category.assoc]

/-- The category of witnessed normalized towers, with levelwise composition of pairs. -/
noncomputable instance (T : Scheme.{u}) (d : Scheme.AdicCoefficientDatum A) :
    Category (PbcWitnessedTower T d) where
  Hom := PbcWitnessedTowerHom
  id := pbcWitnessedTowerId
  comp := pbcWitnessedTowerComp
  id_comp := (pbcWitnessedTower_category_laws T d).1 _ _
  comp_id := (pbcWitnessedTower_category_laws T d).2.1 _ _
  assoc := (pbcWitnessedTower_category_laws T d).2.2 _ _ _ _

end AlgebraicGeometry.ProEtale
