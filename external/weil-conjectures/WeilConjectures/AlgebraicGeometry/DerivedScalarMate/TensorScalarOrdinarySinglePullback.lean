/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison

/-! # Ordinary tensor pullback with a single coefficient

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-sfb-tensor-scalar-ordinary-single-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
section Proof

-- Use countable colimits directly instead of diagram-wide instance search.
private theorem ordinaryTensorTotal {W : Scheme.{u}}
    (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules W A) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (proEtaleOrdinaryTensor W A) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} (proEtaleRingModules W A)) _ _) _

attribute [local instance] ordinaryTensorTotal
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingExtension proEtaleRingRestrictionPullbackInv
  SheafOfModules.monoidalCategory ordinaryTensorIso ordinaryComplexIso
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CochainComplex.mapBifunctorSingle₂Iso
set_option backward.defeqAttrib.useBackward true

private def ordinaryTensorPullbackNat {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (CategoryTheory.Functor.postcompose₂.obj
      (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))).obj
        (proEtaleOrdinaryTensor T A) ⟶
    (((CategoryTheory.Functor.whiskeringLeft₂ (proEtaleRingModules Z (inverseRing f A))).obj
      (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))).obj
      (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))).obj
        (proEtaleOrdinaryTensor Z (inverseRing f A)) where
  app M :=
    { app := fun N ↦ (proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _) M N).hom
      naturality := by
        intro N N' z
        dsimp
        simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
          proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_obj_map,
          MonoidalCategory.curriedTensor_map_app] using
          proEtaleOrdinaryTensorPullback_naturality f A (inverseRing f A) (Iso.refl _)
            M M N N' (𝟙 M) z }
  naturality M M' v := by
    apply NatTrans.ext
    funext N
    dsimp
    have h := proEtaleOrdinaryTensorPullback_naturality
      f A (inverseRing f A) (Iso.refl _) M M' N N v (𝟙 N)
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h

private theorem ordinaryPullback_colimits {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∀ j : ℤ, PreservesColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j}))
      (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)) := fun _ ↦
  (proEtaleRingModuleAdjunction f A (inverseRing f A) (Iso.refl _)
    ).leftAdjoint_preservesColimits.preservesColimitsOfShape

attribute [local instance] ordinaryPullback_colimits

private theorem ordinaryTensorPullbackNat_total {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (P Q : CochainComplex (proEtaleRingModules T A) ℤ) :
    (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _) P Q).inv =
      HomologicalComplex.mapBifunctorComparison (ordinaryTensorPullbackNat f A) (.up ℤ) P Q := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.monoidalCategory (inverseRing f A)
  apply (cancel_epi
    (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _) P Q).hom).mp
  rw [Iso.hom_inv_id]
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.comp_id]
  change _ = _ ≫
    (proEtaleTensorPullbackTotal f A (inverseRing f A) (Iso.refl _) P Q).f n ≫
      HomologicalComplex.mapBifunctorComparisonX (ordinaryTensorPullbackNat f A)
        (.up ℤ) P Q n
  simp only [proEtaleTensorPullbackTotal, tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  erw [Category.assoc, HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  change _ = (proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _)
    (P.X i) (Q.X j)).inv ≫
    (proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _)
      (P.X i) (Q.X j)).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

private theorem cancel_with_inverse {C : Type*} [Category C]
    {X Y Z : C} {a b : X ⟶ Y} (i : Y ⟶ Z) (j : Z ⟶ Y)
    (hij : i ≫ j = 𝟙 Y) (h : a ≫ i = b ≫ i) : a = b := by
  simpa only [Category.assoc, hij, Category.comp_id] using congrArg (· ≫ j) h

end Proof

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint proEtaleRingModulePullback
  proEtaleRingExtension proEtaleRingRestrictionPullbackInv
  SheafOfModules.monoidalCategory ordinaryTensorIso ordinaryComplexIso
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CochainComplex.mapBifunctorSingle₂Iso
set_option backward.defeqAttrib.useBackward true

/-- The single-coefficient total pullback is tensor pullback in every degree.
Source: Stacks Tags 03EL and 07A4
(blueprint: lem-sfb-tensor-scalar-ordinary-single-pullback).

Proof: the inverse total comparison is the bifunctor comparison, as verified on
homogeneous summands. Apply the existing single-factor component comparison.
Functoriality separates the single-complex coefficient isomorphism into its
singleMapHomologicalComplex and coefficientPullback factors. Naturality in the
coefficient and the two inverse identities cancel the target single-factor
isomorphism, leaving ordinary tensor pullback followed by the coefficient map. -/
theorem tensorScalarOrdinaryPullback_single_f {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules T A) ℤ) (n : ℤ) :
    let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
    let FAc := FA.mapHomologicalComplex (.up ℤ)
    (FAc.map (CochainComplex.mapBifunctorSingle₂Iso
      (proEtaleOrdinaryTensor T A) (coefficient a) P).inv ≫
      tensorScalarOrdinaryPullback f a P ≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (proEtaleOrdinaryTensor Z (inverseRing f A)) (coefficient (inverseMap f a))
        (FAc.obj P)).hom).f n =
    (proEtaleOrdinaryTensorPullback f A (inverseRing f A) (Iso.refl _)
      (P.X n) (coefficient a)).hom ≫
      ((proEtaleOrdinaryTensor Z (inverseRing f A)).obj (FA.obj (P.X n))).map
        (coefficientPullback f a).hom := by
  let : ∀ K L : CochainComplex (proEtaleRingModules T A) ℤ,
      HomologicalComplex.HasMapBifunctor K L (proEtaleOrdinaryTensor T A) (.up ℤ) :=
    ordinaryTensorTotal A
  let : ∀ K L : CochainComplex (proEtaleRingModules Z (inverseRing f A)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (proEtaleOrdinaryTensor Z (inverseRing f A)) (.up ℤ) :=
    ordinaryTensorTotal (inverseRing f A)
  dsimp only
  let FA := proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
  let FAc := FA.mapHomologicalComplex (.up ℤ)
  let TZ := proEtaleOrdinaryTensor Z (inverseRing f A)
  let k := coefficientPullback f a
  let sx := CochainComplex.mapBifunctorSingle₂Iso TZ (coefficient (inverseMap f a)) (FAc.obj P)
  let : ∀ j : ℤ, PreservesColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) FA :=
    ordinaryPullback_colimits f A
  have hc := CochainComplex.mapBifunctorComparisonX_single₂
    (ordinaryTensorPullbackNat f A) P (coefficient a) n
  have ht := congrArg (fun z ↦ z.f n)
    (ordinaryTensorPullbackNat_total f A P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (coefficient a)))
  change (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _) P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (coefficient a))).inv.f n =
    HomologicalComplex.mapBifunctorComparisonX (ordinaryTensorPullbackNat f A)
      (.up ℤ) P ((HomologicalComplex.single _ (.up ℤ) 0).obj (coefficient a)) n at ht
  rw [← ht] at hc
  have hk := congrArg (fun z ↦ z.f n)
    (CochainComplex.mapBifunctorSingle₂Iso_inv_naturality₂ TZ k.hom (FAc.obj P))
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f] at hk
  have hsx := congrArg (fun z ↦ z.f n) sx.hom_inv_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hsx
  unfold tensorScalarOrdinaryPullback tensorCoefficientComplexPullback
  simp only [Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.mapIso_hom]
  have hcomp : HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
      (((HomologicalComplex.singleMapHomologicalComplex FA (.up ℤ) 0).app
        (coefficient a)).hom ≫
        (CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A)) (0 : ℤ)).map
          k.hom) TZ (.up ℤ) =
    HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
      ((HomologicalComplex.singleMapHomologicalComplex FA (.up ℤ) 0).app
        (coefficient a)).hom TZ (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 (FAc.obj P))
        ((CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A))
          (0 : ℤ)).map k.hom) TZ (.up ℤ) := by
    exact (TZ.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj (FAc.obj P) |>.map_comp _ _
  erw [hcomp]
  simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.mapHomologicalComplex_map_f,
    Category.assoc]
  have hisx := congrArg (fun z ↦ z.f n) sx.inv_hom_id
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hisx
  apply cancel_with_inverse (sx.inv.f n) (sx.hom.f n) hisx
  simp only [Category.assoc]
  erw [hsx, Category.comp_id]
  erw [reassoc_of% hc, ← hk]
  rfl

end AlgebraicGeometry.Scheme.DerivedScalarMate
