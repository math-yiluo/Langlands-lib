/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupRealizationComplexData
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification

/-! # Cochain obligations for resolution pairings

Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  globalPullbackMatesColimits cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

set_option linter.unusedSectionVars false in
private theorem tensor_hom_ext {M N P : X.Modules} {a b : M ⊗ N ⟶ P}
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      a.app U (tmulSection s t) = b.app U (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv (M.val ⊗ N.val) P).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h U.unop s t

set_option linter.unusedSectionVars false in
private lemma singleTensor_component (F G : SheafOfModules.{u}
    (moduleRings X.toRingedSpace)) :
    HomologicalComplex.ιTensorObj
        ((CochainComplex.singleFunctor _ 0).obj F)
        ((CochainComplex.singleFunctor _ 0).obj G) 0 0 0 (by omega) ≫
      (DerivedCategory.moduleCup_singleTensorIso F G).hom.f 0 =
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ⊗ₘ
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F ⊗ G)).inv := by
  dsimp only [DerivedCategory.moduleCup_singleTensorIso, Iso.trans_hom,
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso, Iso.app,
    NatIso.ofComponents, CochainComplex.mapBifunctorSingle₂Iso,
    Iso.symm_hom, HomologicalComplex.comp_f, CochainComplex.singleFunctor]
  simp only [Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  dsimp only [CochainComplex.mapBifunctorSingle₁Iso, Iso.symm_hom,
    HomologicalComplex.Hom.isoOfComponents]
  dsimp only [Iso.symm_inv, CochainComplex.mapBifunctorSingle₁XIso]
  have hs : (ComplexShape.up ℤ).σ (.up ℤ) (.up ℤ) 0 0 = 1 := by rfl
  rw [hs, one_smul]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [and_self, dite_eq_left,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [whiskerLeft_id, id_whiskerRight, Category.comp_id, Category.id_comp, tensorHom_id]

set_option linter.unusedSectionVars false in
/-- A realization respects the coefficient augmentations before localization.
Source: Stacks Project, Tag 0FKU, construction before Lemma 20.31.3.
(blueprint: lem-sc-module-cup-resolution-augmentation)
Proof: the source tensor of single complexes is concentrated in degree zero. In all
other degrees both maps vanish. In degree zero, test the maps on elementary tensors
of sections over each open. The extension/single and tensor/single isomorphisms send
these tensors to the corresponding degree-zero summand. Apply Realizes at p=q=0,
then augmentation_pair. Elementary tensors generate the presheaf tensor and hence
its sheafification, so equality on these sections gives equality of sheaf morphisms.
Degreewise extensionality gives the cochain identity. -/
theorem moduleCup_resolution_augmentation {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t) :
    (CategoryTheory.MonoidalCategory.tensorHom
      (C := CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.left.augmentation ComplexShape.embeddingUpNat)
      ((HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.right.augmentation ComplexShape.embeddingUpNat)) ≫ t =
      (DerivedCategory.moduleCup_singleTensorIso
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) F G).hom ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (F ⊗ G) 0 0 rfl).inv ≫
        HomologicalComplex.extendMap D.target.augmentation ComplexShape.embeddingUpNat := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      have hn : n = 0 := by simpa [ComplexShape.π_def] using hpq.symm
      subst n
      simp only [HomologicalComplex.comp_f]
      erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
      dsimp only [ComplexShape.π_def, HomologicalComplex.comp_f]
      have hc := singleTensor_component (X := X) F G
      dsimp only [HomologicalComplex.ιTensorObj] at hc
      erw [reassoc_of% hc]
      erw [HomologicalComplex.extendSingleIso_inv_f,
        HomologicalComplex.extendSingleIso_inv_f,
        HomologicalComplex.extendSingleIso_inv_f,
        HomologicalComplex.extendMap_f _ _ (i := (0 : ℕ)) rfl,
        HomologicalComplex.extendMap_f _ _ (i := (0 : ℕ)) rfl,
        HomologicalComplex.extendMap_f _ _ (i := (0 : ℕ)) rfl]
      dsimp only [CochainComplex.single₀, Scheme.Modules]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
      simp only [Category.id_comp, tensorHom_id, id_whiskerRight]
      rw [← Category.assoc, ← tensorHom_def]
      change ((D.left.augmentation.f 0 ≫
          (D.left.K.extendXIso ComplexShape.embeddingUpNat rfl).inv) ⊗ₘ
        (D.right.augmentation.f 0 ≫
          (D.right.K.extendXIso ComplexShape.embeddingUpNat rfl).inv)) ≫
        HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          0 0 0 (by omega) ≫ t.f 0 =
        D.target.augmentation.f 0 ≫
          (D.target.K.extendXIso ComplexShape.embeddingUpNat rfl).inv
      rw [← cancel_mono (D.target.K.extendXIso ComplexShape.embeddingUpNat rfl).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply tensor_hom_ext
      intro V a b
      simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection]
      have hr := ht 0 0 V ((D.left.augmentation.f 0).val.app (op V) a)
        ((D.right.augmentation.f 0).val.app (op V) b)
      exact hr.trans (D.augmentation_pair V a b)
    · apply IsZero.eq_of_src
      exact ((tensorLeft _).map_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq))
  · apply IsZero.eq_of_src
    exact ((tensorRight _).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp))

end
end AlgebraicGeometry.Scheme.Modules
