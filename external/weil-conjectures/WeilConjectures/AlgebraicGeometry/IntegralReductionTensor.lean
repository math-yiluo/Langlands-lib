/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # Integral reduction as a derived tensor functor

Source: Bhatt--Scholze, Lemma 6.5.9(3), and the definition of derived extension
of scalars (auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (M : Mod C R)

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma extendTensorHom_linear :
    γ[R,((comap φ).obj ((extendScalars φ).obj M)).X] ≫
        (extendForgetTensorObjIso φ M).hom =
      R ◁ (extendForgetTensorObjIso φ M).hom ≫
        γ[R,(((comap φ).obj (regular S)) ⊗ M).X] := by
  apply (cancel_epi (R ◁ extendπ φ M)).1
  change R ◁ extendπ φ M ≫ (φ ▷ (extendScalarsObj φ M).X ≫
      γ[S,(extendScalarsObj φ M).X]) ≫ (extendForgetTensorObjIso φ M).hom = _
  simp only [Category.assoc]
  rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc]
  have hπ : extendπ φ M ≫ (extendForgetTensorObjIso φ M).hom =
      tensorObjπ ((comap φ).obj (regular S)) M := by
    simp only [extendForgetTensorObjIso, extendπ_extendDescHom]
  rw [hπ, ← whiskerLeft_comp_assoc, hπ, whiskerLeft_tensorπ_smul]
  change φ ▷ (S ⊗ M.X) ≫ (α_ S S M.X).inv ≫ μ[S] ▷ M.X ≫ _ =
    (α_ R S M.X).inv ≫ (φ ▷ S ≫ μ[S]) ▷ M.X ≫ _
  rw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]

noncomputable def extendComapTensorIso :
    extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular S)) :=
  NatIso.ofComponents
    (fun M ↦ Mod.isoMk (extendForgetTensorObjIso φ M) (extendTensorHom_linear φ M))
    (by
      intro M N f
      apply (forget R).map_injective
      exact (extendForgetTensorIso φ).hom.naturality f)

noncomputable def extendComapCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (extendScalars φ).leftDerivedFunctorCounit
      (comap φ).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((extendScalars φ).mapHomotopyCategory (.up ℤ))
      (comap φ).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (extendScalars φ ⋙ comap φ)) (.up ℤ)).hom
      DerivedCategory.Qh

instance tensorLeft_preservesKFlatQuasiIso (B : Mod C R) :
    (tensorLeft B).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  exact (CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B).of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm

noncomputable def tensorPresentationHomotopyIso :
    (extendScalars φ ⋙ comap φ).mapHomotopyCategory (.up ℤ) ≅
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) :=
  let e := extendComapTensorIso φ
  { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
    inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
    hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
    inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }

noncomputable def tensorPresentationDerivedCounit :
    DerivedCategory.Qh ⋙ ((extendScalars φ).leftDerivedFunctor ⋙
        (comap φ).mapDerivedCategory) ⟶
      (tensorLeft ((comap φ).obj (regular S))).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  extendComapCounit φ ≫
    Functor.whiskerRight (tensorPresentationHomotopyIso φ).hom DerivedCategory.Qh

lemma tensorPresentationDerivedCounit_isLeftDerivedFunctor :
    ((extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory).IsLeftDerivedFunctor
      (tensorPresentationDerivedCounit φ) (HomotopyCategory.quasiIso (Mod C R) (.up ℤ)) := by
  apply ((tensorLeft ((comap φ).obj (regular S))).isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    (tensorPresentationDerivedCounit φ)).2
  intro K hK
  have := (extendScalars φ).isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  dsimp only [tensorPresentationDerivedCounit, extendComapCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

end CategoryTheory.Mod

local instance instEssentiallySmallProfinite_algebraicGeometryIntegralReductionTensor
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing
