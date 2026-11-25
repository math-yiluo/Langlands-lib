/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorFlatModelMaps
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal

/-! # The right quotient tensor path on flat models

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
attribute [local semireducible] AlgebraicGeometry.ProEtale.QuotientChange.L

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

private theorem paste_right
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory E]
    (U : A ⥤ C) [U.LaxMonoidal] (V : B ⥤ E) [V.LaxMonoidal]
    (F : A ⥤ B) (G : C ⥤ E) (γ : U ⋙ G ⟶ F ⋙ V)
    (δ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj G).obj G).obj (curriedTensor E))
    {x y z : C} {P Q T : A} {p q : B}
    (s : x ⟶ U.obj P) (t : y ⟶ U.obj Q) (b : z ⟶ x ⊗ y)
    (v : z ⟶ U.obj T) (d₀ : T ⟶ P ⊗ Q)
    (d : F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (r : F.obj P ⟶ p) (r' : F.obj Q ⟶ q)
    (hb : b ≫ (s ⊗ₘ t) ≫ Functor.LaxMonoidal.μ U P Q = v ≫ U.map d₀)
    (hc : (δ.app (U.obj P)).app (U.obj Q) ≫ (γ.app P ⊗ₘ γ.app Q) ≫
        Functor.LaxMonoidal.μ V (F.obj P) (F.obj Q) =
      G.map (Functor.LaxMonoidal.μ U P Q) ≫ γ.app (P ⊗ Q) ≫ V.map d) :
    G.map b ≫ (δ.app x).app y ≫
        ((G.map s ≫ γ.app P ≫ V.map r) ⊗ₘ (G.map t ≫ γ.app Q ≫ V.map r')) ≫
        Functor.LaxMonoidal.μ V p q =
      G.map v ≫ γ.app T ≫ V.map (F.map d₀ ≫ d ≫ (r ⊗ₘ r')) := by
  have hn : G.map (s ⊗ₘ t) ≫ (δ.app (U.obj P)).app (U.obj Q) =
      (δ.app x).app y ≫ (G.map s ⊗ₘ G.map t) := by
    have h₁ := congr_app (δ.naturality s) y
    have h₂ := (δ.app (U.obj P)).naturality t
    dsimp at h₁ h₂
    rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc, h₂,
      reassoc_of% h₁, MonoidalCategory.tensorHom_def]
  have hγ := γ.naturality d₀
  dsimp only [Functor.comp_map] at hγ
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural, ← reassoc_of% hn, reassoc_of% hc]
  simp only [← G.map_comp_assoc]
  rw [hb]
  simp only [G.map_comp, Category.assoc]
  rw [reassoc_of% hγ]
  simp only [Functor.map_comp]

namespace AlgebraicGeometry.ProEtale.QuotientTensorFlatModel

open QuotientChange QuotientSectionTensor IntegralQuotient

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

private theorem q_hom {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ :=
  Quotient.lift.isLift_hom _ _ _ P

private theorem q_inv {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso C).inv.app P = 𝟙 _ :=
  Quotient.lift.isLift_inv _ _ _ P

private theorem q_map {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {P Q : CochainComplex C ℤ} (g : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g) =
      DerivedCategory.Q.map g := rfl

private theorem q_obj {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P) =
      DerivedCategory.Q.obj P := rfl

private theorem homotopy_obj
    {C E : Type*} [Category C] [Category E] [Preadditive C] [Preadditive E]
    (F : C ⥤ E) [F.Additive] (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).obj ((F.mapHomologicalComplex (.up ℤ)).obj P) := rfl

private theorem cochain_app
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    (F : C ⥤ E) [F.Additive] (G : DerivedCategory C ⥤ DerivedCategory E)
    (ε : DerivedCategory.Qh ⋙ G ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    G.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso E).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient _ _).obj P) := by
  change G.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [G.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

private theorem homotopy_tensor
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    (HomotopyCategory.quotient C (.up ℤ)).obj P ⊗
        (HomotopyCategory.quotient C (.up ℤ)).obj Q =
      (HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q) := rfl

private theorem q_tensor
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q) := by
  rw [Functor.tensorator_Q, q_inv, q_inv, q_hom, id_tensorHom_id, Category.id_comp]
  erw [Category.comp_id]

private theorem scalar_compute_eq
    (a : R ⟶ S) [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules R T) ℤ) :
    compute a T P = (scalarCounit a T).app ((HomotopyCategory.quotient _ _).obj P) := by
  exact cochain_app (extension a T) (D a T) (scalarCounit a T) P

private theorem pull_compute_eq
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules B Y) ℤ) :
    computePull f P = (pullCounit (Λ := B) f).app
      ((HomotopyCategory.quotient _ _).obj P) := by
  exact cochain_app (CondensedRing.upperStar B f) (L B f) (pullCounit f) P

private theorem map_comp_hom
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive E]
    {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ C} {I : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : CochainComplex A ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := rfl

private theorem factor_normalized
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (hlam : PullNormalized a f lam) (P : CochainComplex (Modules R Y) ℤ) :
    lam.hom.app (DerivedCategory.Q.obj P) ≫ factorCompute a f P =
      (L S f).map (compute a Y P) ≫ computePull f ((scalarComplex a Y).obj P) ≫
        DerivedCategory.Q.map (totalBalance a f P) := by
  have h := hlam ((HomotopyCategory.quotient _ _).obj P)
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at h
  simpa only [factorCompute, scalar_compute_eq, pull_compute_eq,
    map_comp_hom, Iso.symm_hom, q_map, homotopy_obj, q_obj, totalBalance,
    Functor.comp_obj, Category.assoc] using h

private theorem pull_counit_app
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules B Y) ℤ) :
    (derivedCochainCounit (CondensedRing.upperStar B f) (L B f)
      (pullCounit (Λ := B) f)).app P = computePull f P := by
  simp only [derivedCochainCounit, derivedCochainComparisonFactors, computePull,
    NatTrans.comp_app, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

private theorem pull_tensor_computation
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (Modules B Y) ℤ) :
    ((CondensedRing.leftDerivedUpperStarTensor B f).app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
        (computePull f P ⊗ₘ computePull f Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((pullComplex f B).obj P) ((pullComplex f B).obj Q) =
      (L B f).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        computePull f (P ⊗ Q) ≫ DerivedCategory.Q.map (totalPull f B P Q) := by
  let := CondensedRing.monoidal_upperStar B f
  let := CondensedRing.upperStar_preservesFlat B f
  have h := (CondensedRing.upperStar B f).leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)
  rw [CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
  simpa only [pull_compute_eq, q_tensor,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app, q_map,
    pullCounit, L, CondensedRing.moduleObjectDerivedPullback, id_eq,
    totalPull, homotopy_obj, homotopy_tensor, q_obj, Functor.comp_obj,
    CondensedRing.leftDerivedUpperStarTensorLeft, Functor.leftDerivedDerivedTensor] using h

/-- Compute the path that takes the two tensorators before balancing the factors.
Only the scalar tensor normalization at Y enters this statement. -/
theorem right_flat_computation
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]
    (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L S f ≅ L R f ⋙ D a X)
    (hlam : PullNormalized a f lam)
    (bY : TensorIso a Y) (hbY : QuotientSectionTensor.TensorNormalized a Y bY)
    (P Q : CochainComplex (Modules R Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hPflat : ∀ i : ℤ, ObjectProperty.flat (P.X i))
    (hQflat : ∀ i : ℤ, ObjectProperty.flat (Q.X i))
    [IsIso (targetLocalization a f P Q)] :
    (L S f).map (bY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        ((CondensedRing.leftDerivedUpperStarTensor S f).app
          ((D a Y).obj (DerivedCategory.Q.obj P))).app
            ((D a Y).obj (DerivedCategory.Q.obj Q)) ≫
        (lam.hom.app (DerivedCategory.Q.obj P) ⊗ₘ
          lam.hom.app (DerivedCategory.Q.obj Q)) ≫ targetCompute a f P Q =
      sourceCompute a f P Q ≫ DerivedCategory.Q.map (ordinaryRight a f P Q) ≫
        targetTensor a f P Q := by
  let γ := derivedCochainCounit (CondensedRing.upperStar S f) (L S f)
    (pullCounit (Λ := S) f)
  have hc := pull_tensor_computation S f ((scalarComplex a Y).obj P)
    ((scalarComplex a Y).obj Q)
  have hb := hbY P Q hP hQ hPflat hQflat
  have h := paste_right (DerivedCategory.Q (C := Modules S Y))
    (DerivedCategory.Q (C := Modules S X)) (pullComplex f S) (L S f) γ
    (CondensedRing.leftDerivedUpperStarTensor S f)
    (compute a Y P) (compute a Y Q)
    (bY.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
    ((D a Y).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ compute a Y (P ⊗ Q))
    (totalScalar a Y P Q)
    (totalPull f S ((scalarComplex a Y).obj P) ((scalarComplex a Y).obj Q))
    (totalBalance a f P) (totalBalance a f Q)
    (by simpa only [Category.assoc] using hb)
    (by simpa only [γ, pull_counit_app] using hc)
  simp only [γ, pull_counit_app] at h
  apply (cancel_mono (targetLocalization a f P Q)).mp
  simp only [Category.assoc, targetTensor, IsIso.inv_hom_id, Category.comp_id]
  rw [targetCompute, tensorHom_comp_tensorHom_assoc,
    factor_normalized a f lam hlam P, factor_normalized a f lam hlam Q]
  simpa only [sourceCompute, ordinaryRight, Functor.map_comp, Category.assoc] using h

end AlgebraicGeometry.ProEtale.QuotientTensorFlatModel
