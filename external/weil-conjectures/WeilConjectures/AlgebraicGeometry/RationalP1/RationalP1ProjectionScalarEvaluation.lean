/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData

import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal

/-! # Scalar evaluation of the normalized projective-line projection mate
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
  projectionMateMap
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory

private theorem scalar_evaluation_aux
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    (φ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (hη : ∀ X : C, (φ.app X).app (𝟙_ C) ≫ F.obj X ◁ η ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (M : D) (K : C) (t : K ⟶ 𝟙_ C) :
    ((adj.rightAdjointProjectionMap φ).app M).app K ≫
      R.map (M ◁ (F.map t ≫ η) ≫ (ρ_ M).hom) =
      (R.obj M ◁ t) ≫ (ρ_ (R.obj M)).hom := by
  have hn := ((adj.rightAdjointProjectionMap φ).app M).naturality t
  change (R.obj M ◁ t) ≫ ((adj.rightAdjointProjectionMap φ).app M).app (𝟙_ C) =
    ((adj.rightAdjointProjectionMap φ).app M).app K ≫ R.map (M ◁ F.map t) at hn
  simp only [whiskerLeft_comp, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  exact congrArg (fun z ↦ (R.obj M ◁ t) ≫ z)
    (adj.rightAdjointProjectionMap_rightUnitality φ η hη M)

attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem native_unit_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    HEq (secondTraceUnitIso Λ Y)
      (CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y)) := by
  unfold secondTraceUnitIso secondTracePullMonoidal internalMonoidal
    internalTensorBundle nativeTensorBundle moduleObjectDerivedPullback
  rfl

section NativeProjection
attribute [local semireducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [-instance] internalMonoidal internalTensorCommShift
attribute [local instance 20000] ProEtale.sheafBraidedCategory
attribute [local instance 3000] projectionDerivedMonoidal
attribute [local instance 4000] projectionModuleAbelian projectionModuleMonoidal
  projectionModuleHasDerived
attribute [local instance 5000] projectionSheafMonoidal projectionCoefficientMonObj
  projectionModuleCategory

@[instance_reducible]
private def native_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }
attribute [local instance 20001] native_sheaf_symmetric

private theorem native_projection_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Modules Λ X)) (K : DerivedCategory (Modules Λ Y))
    (t : K ⟶ 𝟙_ (DerivedCategory (Modules Λ Y))) :
    moduleObjectProjectionMate Λ f M K ≫
      (moduleObjectDerivedPushforward Λ f).map
        (M ◁ ((moduleObjectDerivedPullback Λ f).map t ≫
          (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom) ≫ (ρ_ M).hom) =
      ((moduleObjectDerivedPushforward Λ f).obj M ◁ t) ≫
        (ρ_ ((moduleObjectDerivedPushforward Λ f).obj M)).hom := by
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  let := leftDerivedUpperStarOplaxMonoidal Λ f
  have hu (N : DerivedCategory (Modules Λ Y)) :=
    Functor.OplaxMonoidal.right_unitality_hom (CondensedRing.upperStar Λ f).leftDerivedFunctor N
  rw [leftDerivedUpperStarOplaxMonoidal_η] at hu
  exact scalar_evaluation_aux (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f)
    (moduleObjectDerivedTensorComparison Λ f) (CondensedRing.leftDerivedUpperStarUnitIso Λ f).hom
    hu M K t

end NativeProjection

attribute [local semireducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward in
private theorem normalized_projection_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (a : ProjectionMateFamily Λ) (ha : ProjectionMateNormalized Λ a)
    (U : (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      (𝟙_ (DerivedCategory (Modules Λ Y))) ≅
      𝟙_ (DerivedCategory (Modules Λ (ProjectiveLine Y))))
    (hU : HEq U (CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y)))
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (K : DerivedCategory (Modules Λ Y))
    (t : K ⟶ 𝟙_ (DerivedCategory (Modules Λ Y))) :
    a (ProjectiveLine Y ↘ Y) M K ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map t ≫ U.hom) ≫
          (ρ_ M).hom) =
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M ◁ t) ≫
        (ρ_ ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)).hom := by
  unfold ProjectionMateFamily ProjectionMateNormalized internalMonoidal
    internalTensorBundle nativeTensorBundle moduleObjectDerivedPullback
    moduleObjectDerivedPushforward at *
  have hm : a (ProjectiveLine Y ↘ Y) M K =
      moduleObjectProjectionMate Λ (ProjectiveLine Y ↘ Y) M K :=
    eq_of_heq (ha (ProjectiveLine Y ↘ Y) M K)
  have hunit : U = CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y) :=
    eq_of_heq hU
  rw [hm, hunit]
  exact native_projection_evaluation Λ (ProjectiveLine Y ↘ Y) M K t

private theorem scalar_paste_aux
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) (M : D) (K S T : C) (A : S ⟶ T)
    (B : T ⟶ R.obj M ⊗ K) (V W : D) (b : F.obj K ⟶ V)
    (v : V ⟶ W) (w : W ⟶ 𝟙_ D) (t : K ⟶ 𝟙_ C)
    (η : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (π : R.obj M ⊗ K ⟶ R.obj (M ⊗ F.obj K))
    (he : π ≫ R.map (M ◁ (F.map t ≫ η) ≫ (ρ_ M).hom) =
      (R.obj M ◁ t) ≫ (ρ_ (R.obj M)).hom)
    (ht : b ≫ v ≫ w = F.map t ≫ η) :
    A ≫ B ≫ π ≫ R.map (M ◁ b) ≫ R.map ((M ◁ v) ≫ (M ◁ w) ≫ (ρ_ M).hom) =
      A ≫ B ≫ (R.obj M ◁ t) ≫ (ρ_ (R.obj M)).hom := by
  have hs : (M ◁ b) ≫ (M ◁ v) ≫ (M ◁ w) ≫ (ρ_ M).hom =
      (M ◁ (F.map t ≫ η)) ≫ (ρ_ M).hom := by
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc, Category.assoc, ht]
  rw [← Functor.map_comp, hs, he]

/-- Evaluating a scalar after the fixed right projection mate. -/
theorem projectionMate_scalar_evaluation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (S T : DerivedCategory (Modules (coefficient l c).X Y))
    (A : S ⟶ T)
    (B : T ⟶ (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ⊗ K)
    (V W : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (b : (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K ⟶ V)
    (v : V ⟶ W) (w : W ⟶ 𝟙_ (DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y))))
    (t : K ⟶ 𝟙_ (DerivedCategory (Modules (coefficient l c).X Y)))
    (ht : b ≫ v ≫ w =
      (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map t ≫
        (secondTraceUnitIso (coefficient l c).X Y).hom) :
    A ≫ B ≫ projectionMateMap (coefficient l c).X (ProjectiveLine Y ↘ Y) M K ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (M ◁ b) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        ((M ◁ v) ≫ (M ◁ w) ≫ (ρ_ M).hom) =
      A ≫ B ≫ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
      t) ≫
        (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom
      := by
  unfold projectionMateMap
  have he := normalized_projection_evaluation (coefficient l c).X Y
    (projectionMate_existsUnique (coefficient l c).X).exists.choose
    (projectionMate_existsUnique (coefficient l c).X).exists.choose_spec
    (secondTraceUnitIso (coefficient l c).X Y)
    (native_unit_comparison (coefficient l c).X Y) M K t
  exact scalar_paste_aux
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y))
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y))
    M K S T A B V W b v w t (secondTraceUnitIso (coefficient l c).X Y).hom
    ((projectionMate_existsUnique (coefficient l c).X).exists.choose
      (ProjectiveLine Y ↘ Y) M K) he ht

end AlgebraicGeometry.ProEtale.RationalP1
