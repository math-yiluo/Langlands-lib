/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPresentation
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided

/-! # A common homotopy-level model for the residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(auxiliary; not a blueprint node)
-/

@[expose] public section

noncomputable section

universe v u u₁ u₂
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v + 1} C] [Abelian C] [IsGrothendieckAbelian.{v + 1} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

-- Preserve the closed proof appearing in previously compiled consumer signatures.
local instance instBraidedCategoryDerivedCategory_sheaf :
    BraidedCategory (DerivedCategory D) :=
  DerivedMonoidal.braidedCategory' (DerivedCategory.Qh (C := D))
    (HomotopyCategory.quasiIso D (.up ℤ))

attribute [local instance] CategoryTheory.derivedTensorPresentationBraiding

/-- The existing homotopy monoidal structure, with its base-category data fixed.
Source: the homotopy tensor construction used by `tensorModelTarget` below.
(auxiliary; not a blueprint node) -/
noncomputable abbrev tensorModelHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory D (.up ℤ)) :=
  inferInstance

/-- The fixed coefficient concentrated in degree zero in the homotopy category.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(auxiliary; not a blueprint node) -/
noncomputable abbrev tensorModelCoefficient (B : C) :=
  (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)

/-- The standard comparison between the two degree-zero presentations.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(auxiliary; not a blueprint node) -/
noncomputable def tensorModelCoefficientIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj (tensorModelCoefficient B) :=
  CategoryTheory.homotopySingleComparisonIso B

omit [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D] in
set_option backward.isDefEq.respectTransparency false in
/-- The single-object comparison commutes with the exact-functor counit.

Expand the exact single comparison, use the counit factorization through the
map on derived categories, and apply naturality of the single/quotient comparisons.
The inverse coefficient isomorphism is the resulting homotopy comparison.

Source: Bhatt--Scholze, Remark 6.8.15; exact-functor single comparison.
(auxiliary; not a blueprint node) -/
theorem tensorModelCoefficientIso_counit (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (B : C) (B' : D)
    (e : F.obj B ≅ B') :
    let c := F.singleFunctorCompLeftDerivedFunctorIso.app B ≪≫
      (DerivedCategory.singleFunctor D 0).mapIso e
    let eH := (F.mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj B) ≪≫
      (HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((F.mapCochainComplexSingleFunctor 0).app B ≪≫
          (HomologicalComplex.single D (.up ℤ) 0).mapIso e)
    c.inv ≫ F.leftDerivedFunctor.map (Functor.tensorModelCoefficientIso B).hom ≫
      F.leftDerivedFunctorCounit.app (Functor.tensorModelCoefficient B) =
      (Functor.tensorModelCoefficientIso B').hom ≫ DerivedCategory.Qh.map eH.inv := by
  dsimp only
  have h := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    (Functor.tensorModelCoefficient B)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [← h]
  simp only [Functor.singleFunctorCompLeftDerivedFunctorIso, NatIso.trans_app, Iso.trans_inv,
    Iso.trans_hom, Iso.app_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.mapIso_inv, Functor.tensorModelCoefficientIso,
    CategoryTheory.homotopySingleComparisonIso,
    Category.assoc]
  erw [F.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Functor.tensorModelCoefficient, Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.app_hom, NatTrans.id_app,
    Iso.symm_hom, Category.id_comp, Functor.map_comp, Category.assoc]
  erw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    F.mapDerivedCategory.map_id, Category.id_comp,
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app_assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc]

/-- The ordinary tensor model built from a functor on derived categories and
its counit to the homotopy image of F. The definition uses those named data directly.
Source: Bhatt--Scholze, Remark 6.8.15; the standard tensor/counit comparison.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def tensorModelTargetWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (P : HomotopyCategory C (.up ℤ)) :
    G.obj (DerivedCategory.Qh.obj P) ⊗
        G.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  (β_ (G.obj ((DerivedCategory.singleFunctor C 0).obj B))
    (G.obj (DerivedCategory.Qh.obj P))).inv ≫
    ((G.map (tensorModelCoefficientIso B).hom ≫ γ.app (tensorModelCoefficient B)) ⊗ₘ
      γ.app P) ≫
    LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)

/-- Compare the derived target with the ordinary tensor after applying F.
The final tensor factor is K-flat on the representatives used below.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def tensorModelTarget (B : C) (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  tensorModelTargetWith F F.leftDerivedFunctor F.leftDerivedFunctorCounit B P

/-- The target comparison is invertible on representatives with K-flat image.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(auxiliary; not a blueprint node) -/
theorem tensorModelTarget_isIso (B : C) (P : HomotopyCategory C (.up ℤ))
    (hP : F.kFlatMap P) : IsIso (tensorModelTarget F B P) := by
  have := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B)) _ hP
  have : IsIso (F.leftDerivedFunctorCounit.app (tensorModelCoefficient B)) :=
    inferInstance
  have : IsIso (F.leftDerivedFunctorCounit.app P) := inferInstance
  have : IsIso (LaxMonoidal.μ (DerivedCategory.Qh (C := D))
      ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B))
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) := ‹_›
  unfold tensorModelTarget tensorModelTargetWith
  infer_instance

variable [F.IsLeftAdjoint] [F.Monoidal]

/-- The common map: the tensor counit, the exact-F counit, then the ordinary
comonoidal comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def tensorModelMapWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    G.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  G.map (ε.app P) ≫ γ.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)

end CategoryTheory.Functor

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

variable (P : HomotopyCategory
  (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))

end AlgebraicGeometry.ProEtale.CondensedRing

noncomputable section Generic
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
local instance : BraidedCategory (DerivedCategory C) :=
  derivedTensorPresentationBraiding
local instance : BraidedCategory (DerivedCategory D) :=
  derivedTensorPresentationBraiding
-- Allow elaboration of the explicitly constructed module tensor comparisons.
/-- Normalize a tensor route by its tensor/counit square and the ordinary braiding.

Naturality moves the single comparison through the tensorator. The braiding equation
moves the coefficient to the first factor. The tensor/counit square then replaces the
comparison by the ordinary tensor map. The tensor presentation's defining equation and
naturality of the counit give the displayed model map.

Source: Bhatt--Scholze, Remark 6.8.15; the canonical derived tensor/counit equations.
(auxiliary; not a blueprint node) -/
theorem CategoryTheory.Functor.tensorModelRoute_fac (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [G.OplaxMonoidal]
    (hδ : ∀ K L : HomotopyCategory C (.up ℤ),
      Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj L) ≫
        (γ.app K ⊗ₘ γ.app L) ≫ Functor.LaxMonoidal.μ DerivedCategory.Qh
          ((F.mapHomotopyCategory (.up ℤ)).obj K)
          ((F.mapHomotopyCategory (.up ℤ)).obj L) =
        G.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K L) ≫ γ.app (K ⊗ L) ≫
          DerivedCategory.Qh.map
            (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app K).app L))
    (hG : ∀ X Y : C, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ))
 :
    G.map
          ((derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj P)
          ((DerivedCategory.singleFunctor C 0).obj B) ≫
        Functor.tensorModelTargetWith F G γ B P = Functor.tensorModelMapWith F G γ B H ε P := by
  have hbr := Functor.mapHomotopyCategory_map_braiding_hom_δ F hG
    (Functor.tensorModelCoefficient B) P
  have hb : ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app
          (Functor.tensorModelCoefficient B) ≫
        (β_ ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B))
          ((F.mapHomotopyCategory (.up ℤ)).obj P)).inv =
      (F.mapHomotopyCategory (.up ℤ)).map
          (β_ (Functor.tensorModelCoefficient B) P).inv ≫
        ((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (Functor.tensorModelCoefficient B)).app P := by
    rw [← cancel_epi ((F.mapHomotopyCategory (.up ℤ)).map
      (β_ (Functor.tensorModelCoefficient B) P).hom)]
    rw [← (F.mapHomotopyCategory (.up ℤ)).map_comp_assoc, Iso.hom_inv_id,
      (F.mapHomotopyCategory (.up ℤ)).map_id, Category.id_comp]
    erw [reassoc_of% hbr, Iso.hom_inv_id, Category.comp_id]
    rfl
  unfold Functor.tensorModelTargetWith Functor.tensorModelMapWith
  rw [← BraidedCategory.braiding_inv_naturality_assoc]
  rw [show (γ.app P ⊗ₘ
      (G.map (Functor.tensorModelCoefficientIso B).hom ≫
        γ.app (Functor.tensorModelCoefficient B))) =
      G.obj (DerivedCategory.Qh.obj P) ◁
        G.map (Functor.tensorModelCoefficientIso B).hom ≫
      (γ.app P ⊗ₘ
        γ.app (Functor.tensorModelCoefficient B)) by
    simp only [MonoidalCategory.tensorHom_def', MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    rfl]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right_assoc]
  have hμ (K L : HomotopyCategory D (.up ℤ)) :
      (β_ (DerivedCategory.Qh.obj L) (DerivedCategory.Qh.obj K)).inv ≫
          Functor.LaxMonoidal.μ DerivedCategory.Qh L K =
        Functor.LaxMonoidal.μ DerivedCategory.Qh K L ≫
          DerivedCategory.Qh.map (β_ L K).inv :=
    DerivedMonoidal.braidingInvNatTrans_fac DerivedCategory.Qh
      (HomotopyCategory.quasiIso D (.up ℤ)) K L
  erw [hμ ((F.mapHomotopyCategory (.up ℤ)).obj P)
    ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B))]
  rw [reassoc_of% (hδ P (Functor.tensorModelCoefficient B))]
  rw [← DerivedCategory.Qh.map_comp, hb, DerivedCategory.Qh.map_comp]
  have hn := γ.naturality
    (β_ (Functor.tensorModelCoefficient B) P).inv
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hμC (K L : HomotopyCategory C (.up ℤ)) :
      (β_ (DerivedCategory.Qh.obj L) (DerivedCategory.Qh.obj K)).inv ≫
          Functor.LaxMonoidal.μ DerivedCategory.Qh L K =
        Functor.LaxMonoidal.μ DerivedCategory.Qh K L ≫
          DerivedCategory.Qh.map (β_ L K).inv :=
    DerivedMonoidal.braidingInvNatTrans_fac DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) K L
  simp only [← G.map_comp_assoc]
  rw [← hμC P (Functor.tensorModelCoefficient B),
    BraidedCategory.braiding_inv_naturality_right_assoc]
  simp only [Functor.tensorModelCoefficientIso]
  rw [derivedTensorPresentationIso_fac B H ε P]
  simp only [G.map_comp, Category.assoc,
    DerivedCategory.Qh.map_comp]
  have hn' := γ.naturality ((homotopyTensorSingleIso B).inv.app P)
  dsimp only [Functor.comp_map] at hn'
  change _ ≫ γ.app (Functor.tensorModelCoefficient B ⊗ P) = _ at hn'
  rw [reassoc_of% hn']

end Generic
