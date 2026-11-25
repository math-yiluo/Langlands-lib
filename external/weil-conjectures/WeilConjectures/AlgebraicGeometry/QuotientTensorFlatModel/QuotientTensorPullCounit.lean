/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorFlatModelMaps
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal

/-! # The geometric tensor/counit equation on cochains

Transport the native derived pullback tensor comparison's homotopy counit equation
through the quotient comparison isomorphisms. No flatness of the input complexes
is required for this equation.

## References

* Stacks Project 07A4 and 0G7E
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars CategoryTheory.Mod.comap
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.monoidal_upperStar
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.rightExact_cochainCounit
  AlgebraicGeometry.ProEtale.QuotientChange.compute
  AlgebraicGeometry.ProEtale.IntegralQuotient.computePull
  AlgebraicGeometry.ProEtale.QuotientChange.scalarCounit
  AlgebraicGeometry.ProEtale.QuotientChange.pullCounit
attribute [local semireducible] AlgebraicGeometry.ProEtale.QuotientChange.L

universe u v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientTensorFlatModel

open QuotientChange QuotientSectionTensor

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

private theorem factors_id {C E : Type*} [Category C] [Category E]
    [Preadditive C] [Preadditive E] (F : C ⥤ E) [F.Additive]
    (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := by
  simp [Functor.mapHomotopyCategoryFactors]
  rfl

private theorem factors_tail {C E : Type*} [Category C] [Category E]
    [Preadditive C] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ E) [F.Additive] (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso E).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (DerivedCategory.quotientCompQhIso E).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [factors_id]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]

private theorem computePull_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules R Y) ℤ) :
    IntegralQuotient.computePull f P =
      (CondensedRing.upperStar R f).rightExact_cochainCounit P := by
  unfold IntegralQuotient.computePull Functor.rightExact_cochainCounit pullCounit L
    CondensedRing.moduleObjectDerivedPullback
  rw [factors_tail]
  rfl

private theorem cochain_tensor_counit
    {C : Type v₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {E : Type v₂} [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
    [MonoidalClosed E] [BraidedCategory E] [Abelian.HasFunctorialFlatResolution E]
    (F : C ⥤ E) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : CochainComplex C ℤ) :
    F.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        F.rightExact_cochainCounit (P ⊗ Q) ≫
        DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      (F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
          (DerivedCategory.Q.obj Q) ≫
        (F.rightExact_cochainCounit P ⊗ₘ F.rightExact_cochainCounit Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
  let p := HomotopyCategory.quotient C (.up ℤ)
  let q := HomotopyCategory.quotient E (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  let e' := DerivedCategory.quotientCompQhIso E
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom (p.obj P) (p.obj Q)
  have ht := CategoryTheory.transport_tensor_counit
    F.leftDerivedFunctor (e.app P) (e.app Q) (e.app (P ⊗ Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q)))
    (e'.app (((F.mapHomologicalComplex (.up ℤ)).obj P) ⊗
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (Functor.LaxMonoidal.μ DerivedCategory.Qh (p.obj P) (p.obj Q))
    (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
      (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (F.leftDerivedFunctorCounit.app (p.obj P))
    (F.leftDerivedFunctorCounit.app (p.obj Q))
    (F.leftDerivedFunctorCounit.app (p.obj (P ⊗ Q)))
    (DerivedCategory.Qh.map (q.map δ)) (DerivedCategory.Q.map δ)
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Qh.obj (p.obj P))).app
      (DerivedCategory.Qh.obj (p.obj Q)))
    ((F.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj Q))
    (F.leftDerivedTensorComparison_naturality_tensorHom (e.inv.app P) (e.inv.app Q)) h
    (DerivedCategory.quotientCompQhIso_hom_naturality δ)
  rw [Functor.tensorator_Q, Functor.tensorator_Q]
  unfold Functor.rightExact_cochainCounit
  dsimp only [p, q, e, e', δ, Iso.app_hom, Iso.app_inv] at ht
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj] at ht ⊢
  simpa only [Category.assoc] using ht

/-- The derived geometric tensor comparison commutes with the specified cochain counits. -/
theorem pull_tensor_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (Modules R Y) ℤ) :
    (L R f).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        IntegralQuotient.computePull f (P ⊗ Q) ≫
        DerivedCategory.Q.map (totalPull f R P Q) =
      ((CondensedRing.leftDerivedUpperStarTensor R f).app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        (IntegralQuotient.computePull f P ⊗ₘ IntegralQuotient.computePull f Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((pullComplex f R).obj P) ((pullComplex f R).obj Q) := by
  let hm := CondensedRing.monoidal_upperStar R f
  let : (CondensedRing.upperStar R f).OplaxMonoidal := hm.toOplaxMonoidal
  have := CondensedRing.upperStar_preservesFlat R f
  rw [computePull_eq, computePull_eq, computePull_eq,
    CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  unfold L CondensedRing.moduleObjectDerivedPullback totalPull
  exact cochain_tensor_counit (CondensedRing.upperStar R f) P Q

end AlgebraicGeometry.ProEtale.QuotientTensorFlatModel
