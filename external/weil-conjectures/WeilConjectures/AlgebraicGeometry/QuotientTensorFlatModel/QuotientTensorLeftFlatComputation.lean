/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorFlatModelMaps
import all WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorPullCounit
import all WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence

/-! # The left quotient tensor path on flat models

## References

* Stacks 03EL, 06YY, 07A4 and 0G7E
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

private theorem scalar_naturality (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u})
    {P Q : CochainComplex (Modules R T) ℤ} (g : P ⟶ Q) :
    (D a T).map (DerivedCategory.Q.map g) ≫ compute a T Q =
      compute a T P ≫ DerivedCategory.Q.map ((scalarComplex a T).map g) := by
  unfold compute
  simp only [factors_tail, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality,
    CategoryTheory.Functor.map_comp_assoc]
  erw [reassoc_of% (scalarCounit a T).naturality
    ((HomotopyCategory.quotient _ _).map g)]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality]
  rfl

private theorem pull_normalization (a : R ⟶ S) [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L S f ≅ L R f ⋙ D a X) (hlam : PullNormalized a f lam)
    (P : CochainComplex (Modules R Y) ℤ) :
    lam.hom.app (DerivedCategory.Q.obj P) ≫ factorCompute a f P =
      (L S f).map (compute a Y P) ≫
        IntegralQuotient.computePull f ((scalarComplex a Y).obj P) ≫
        DerivedCategory.Q.map (totalBalance a f P) := by
  have h := hlam ((HomotopyCategory.quotient _ _).obj P)
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at h
  unfold factorCompute compute IntegralQuotient.computePull
  simp only [factors_tail, Functor.map_comp, Category.assoc]
  erw [← lam.hom.naturality_assoc]
  simp only [Functor.comp_map]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h]
  have hb : (Functor.mapHomotopyCategoryCompIso
      (CondensedRing.pullIso a f).symm (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map (totalBalance a f P) := rfl
  erw [hb, DerivedCategory.quotientCompQhIso_hom_naturality]
  rfl

/-- Compute the path that balances before the two tensorators.
Only the scalar tensor normalization at X enters this statement. -/
theorem left_flat_computation
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (hlam : PullNormalized a f lam)
    (bX : TensorIso a X) (hbX : QuotientSectionTensor.TensorNormalized a X bX)
    (P Q : CochainComplex (Modules R Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hPflat : ∀ i : ℤ, ObjectProperty.flat (P.X i))
    (hQflat : ∀ i : ℤ, ObjectProperty.flat (Q.X i))
    [IsIso (targetLocalization a f P Q)] :
    lam.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
        (D a X).map (((CondensedRing.leftDerivedUpperStarTensor R f).app
          (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q)) ≫
        bX.hom.app ((L R f).obj (DerivedCategory.Q.obj P),
          (L R f).obj (DerivedCategory.Q.obj Q)) ≫ targetCompute a f P Q =
      sourceCompute a f P Q ≫ DerivedCategory.Q.map (ordinaryLeft a f P Q) ≫
        targetTensor a f P Q := by
  let FP := (pullComplex f R).obj P
  let FQ := (pullComplex f R).obj Q
  have hp := QuotientChange.pull_preserves_kFlat (Λ := R) f P hP
  have hq := QuotientChange.pull_preserves_kFlat (Λ := R) f Q hQ
  have hpf : ∀ i : ℤ, ObjectProperty.flat (FP.X i) := fun i ↦
    Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar R f) (hPflat i)
  have hqf : ∀ i : ℤ, ObjectProperty.flat (FQ.X i) := fun i ↦
    Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar R f) (hQflat i)
  have hs := hbX FP FQ hp hq hpf hqf
  have hn := bX.hom.naturality (Prod.mkHom
    (IntegralQuotient.computePull f P) (IntegralQuotient.computePull f Q))
  simp only [CondensedRing.derivedTensor, Functor.comp_map, Functor.uncurry_obj_map,
    curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] at hn
  change (D a X).map (IntegralQuotient.computePull f P ⊗ₘ
      IntegralQuotient.computePull f Q) ≫
      bX.hom.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) =
    bX.hom.app ((L R f).obj (DerivedCategory.Q.obj P),
      (L R f).obj (DerivedCategory.Q.obj Q)) ≫
      ((D a X).map (IntegralQuotient.computePull f P) ⊗ₘ
        (D a X).map (IntegralQuotient.computePull f Q)) at hn
  apply (cancel_mono (targetLocalization a f P Q)).1
  simp only [targetTensor, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  unfold targetCompute factorCompute
  erw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  erw [← reassoc_of% hn, hs]
  simp only [← Functor.map_comp_assoc]
  erw [← pull_tensor_counit f P Q]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% scalar_naturality a X (totalPull f R P Q)]
  have hl := lam.hom.naturality (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)
  dsimp only [Functor.comp_map] at hl
  have hb := pull_normalization a f lam hlam (P ⊗ Q)
  simp only [factorCompute] at hb
  erw [← reassoc_of% hl, reassoc_of% hb]
  simp only [sourceCompute, ordinaryLeft, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.QuotientTensorFlatModel
