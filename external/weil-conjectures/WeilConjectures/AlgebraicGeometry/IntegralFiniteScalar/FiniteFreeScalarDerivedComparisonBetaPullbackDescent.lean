/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

private theorem app_eq_of_iso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α ρ : F ⟶ G) {A B : C} (i : A ≅ B)
    (h : α.app A = ρ.app A) : α.app B = ρ.app B := by
  apply (cancel_epi (F.map i.hom)).1
  rw [α.naturality, ρ.naturality, h]

/-- If the two displayed morphisms agree on all K-flat representatives, then they agree on
every derived object. -/
theorem finiteFreeScalarDerivedComparison_beta_pullback_of_kflat
    (D : ScalarSixPullbackData.{u}) {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (S : ShortComplex (PointModules Λ))
    (t : S.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (β : ∀ Z : Scheme.{u}, tensorLeft (DerivedCategory.Q.obj (complex Λ S Z)) ≅
      scalarSixChange a Z ⋙ restriction a Z)
    (hβ : ∀ Z, AugmentationNormalized a S t Z (β Z))
    (hrep : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (C : CochainComplex (ModuleRingedComparison.internalModules Λ.X Y) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat C →
      (scalarSixPull Λ f).map ((β Y).hom.app (DerivedCategory.Q.obj C)) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj (DerivedCategory.Q.obj C)) ≫
        (restriction a X).map ((D.theta a f).inv.app (DerivedCategory.Q.obj C)) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) (DerivedCategory.Q.obj C) ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C))) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj (DerivedCategory.Q.obj C))) :
    ∀ (X Y : Scheme.{u}) (f : X ⟶ Y)
      (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)),
      (scalarSixPull Λ f).map ((β Y).hom.app K) ≫
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv.app
          ((scalarSixChange a Y).obj K) ≫
        (restriction a X).map ((D.theta a f).inv.app K) =
      tensorPull Λ f (DerivedCategory.Q.obj (complex Λ S Y)) K ≫
        ((modelPull Λ S f).hom ⊗ₘ 𝟙 ((scalarSixPull Λ f).obj K)) ≫
        (β X).hom.app ((scalarSixPull Λ f).obj K) := by
  have _hβ := hβ
  intro X Y f K
  let F := scalarSixPull Λ f
  let B := DerivedCategory.Q.obj (complex Λ S Y)
  let e := leftDerivedUpperStarIsoMapDerivedCategory Λ.X f
  let τ : tensorLeft B ⋙ F ⟶ F ⋙ tensorLeft (F.obj B) :=
    Functor.whiskerLeft (tensorLeft B) e.inv ≫
      (CondensedRing.upperStar Λ.X f).leftDerivedTensorComparison.app B ≫
        (Functor.tensorHomNatTrans e.hom).app B
  let α : tensorLeft B ⋙ F ⟶
      F ⋙ scalarSixChange a X ⋙ restriction a X :=
    Functor.whiskerRight (β Y).hom F ≫
      Functor.whiskerLeft (scalarSixChange a Y)
        (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv ≫
      Functor.whiskerRight (D.theta a f).inv (restriction a X)
  let ρ : tensorLeft B ⋙ F ⟶
      F ⋙ scalarSixChange a X ⋙ restriction a X :=
    τ ≫ Functor.whiskerLeft F ((curriedTensor _).map (modelPull Λ S f).hom) ≫
      Functor.whiskerLeft F (β X).hom
  obtain ⟨P, p, hp, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have := hp
  let i := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have h : α.app (DerivedCategory.Q.obj P) = ρ.app (DerivedCategory.Q.obj P) := by
    simpa only [α, ρ, τ, F, B, e, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.tensorHomNatTrans_app_app,
      curriedTensor_map_app, tensorHom_id, Category.assoc, tensorPull,
      Functor.comp_obj, tensorLeft, curriedTensor_obj_obj] using hrep X Y f P hP
  suffices hk : α.app K = ρ.app K by
    simpa only [α, ρ, τ, F, B, e, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.tensorHomNatTrans_app_app,
      curriedTensor_map_app, tensorHom_id, Category.assoc, tensorPull,
      Functor.comp_obj, tensorLeft, curriedTensor_obj_obj] using hk
  exact app_eq_of_iso α ρ i h

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
