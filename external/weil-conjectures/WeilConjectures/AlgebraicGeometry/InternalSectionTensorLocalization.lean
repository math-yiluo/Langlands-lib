/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalSliceDerivedHomComparison
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison

set_option linter.privateModule false

/-! # Localization of the sectionwise tensor comparison

Source: Stacks Project, Tags 03CV, 03EK, 06YL, 06YS and 08J9
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local irreducible] CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Mod.monoidalClosed
attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Monoidal.induced
attribute [local implicit_reducible] GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory

section Ordinary

variable {A B : Type*} [Category A] [Category B]
  [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B)
  (e : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
  (e₀ : F.obj (𝟙_ A) ≅ 𝟙_ B)
  (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
    F.map (f ⊗ₘ g) ≫ (e M' N').hom =
      (e M N).hom ≫ (F.map f ⊗ₘ F.map g))
  (ha : ∀ M N P, (e (M ⊗ N) P).hom ≫ (e M N).hom ▷ F.obj P ≫ (α_ _ _ _).hom =
    F.map (α_ M N P).hom ≫ (e M (N ⊗ P)).hom ≫ F.obj M ◁ (e N P).hom)
  (hl : ∀ M, (e (𝟙_ A) M).hom ≫ e₀.hom ▷ F.obj M ≫ (λ_ _).hom =
    F.map (λ_ M).hom)
  (hr : ∀ M, (e M (𝟙_ A)).hom ≫ F.obj M ◁ e₀.hom ≫ (ρ_ _).hom =
    F.map (ρ_ M).hom)

@[instance_reducible]
private def ordinaryMonoidal : F.Monoidal :=
  (Functor.CoreMonoidal.mk' (F := F) e₀.symm (fun M N ↦ (e M N).symm)
    (fun f N ↦ by
      simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, tensorHom_id] using
        (hn _ _ _ _ f (𝟙 N)).symm)
    (fun M f ↦ by
      simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, id_tensorHom] using
        (hn _ _ _ _ (𝟙 M) f).symm)
    ha
    (fun M ↦ by
      apply (cancel_mono (λ_ (F.obj M)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hl,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])
    (fun M ↦ by
      apply (cancel_mono (ρ_ (F.obj M)).hom).mp
      rw [Iso.symm_inv, Iso.symm_inv, Iso.inv_hom_id, Category.assoc, Category.assoc, hr,
        ← F.map_comp, Iso.inv_hom_id, F.map_id])).toMonoidal

private theorem ordinaryMonoidal_delta (M N : A) :
    let := ordinaryMonoidal F e e₀ hn ha hl hr
    Functor.OplaxMonoidal.δ F M N = (e M N).hom := by
  rfl

private structure OrdinaryMonoidalData where
  monoidal : F.Monoidal
  delta : ∀ M N : A, letI := monoidal
    Functor.OplaxMonoidal.δ F M N = (e M N).hom

include e₀ hn ha hl hr in
private theorem ordinary_monoidal_data : Nonempty (OrdinaryMonoidalData F e) := by
  refine ⟨⟨ordinaryMonoidal F e e₀ hn ha hl hr, ?_⟩⟩
  intro M N
  exact ordinaryMonoidal_delta F e e₀ hn ha hl hr M N

end Ordinary

attribute [local irreducible] ordinaryMonoidal

section MonoidalSquare

variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
  (q : C ⥤ D) (r : E ⥤ H) (f : C ⥤ E) (g : D ⥤ H)
  [q.LaxMonoidal] [r.LaxMonoidal] [f.Monoidal] [g.Monoidal]
  (k : q ⋙ g ≅ f ⋙ r) [NatTrans.IsMonoidal k.hom]

private theorem monoidal_square (P Q : C) :
    Functor.OplaxMonoidal.δ g (q.obj P) (q.obj Q) ≫
      (k.hom.app P ⊗ₘ k.hom.app Q) ≫ Functor.LaxMonoidal.μ r (f.obj P) (f.obj Q) =
    g.map (Functor.LaxMonoidal.μ q P Q) ≫ k.hom.app (P ⊗ Q) ≫
      r.map (Functor.OplaxMonoidal.δ f P Q) := by
  have h := NatTrans.IsMonoidal.tensor (τ := k.hom) P Q
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc] at h
  apply (cancel_mono (r.map (Functor.LaxMonoidal.μ f P Q))).mp
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp,
    Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id]
  rw [← h, Functor.Monoidal.δ_μ_assoc]
  let b : g.obj (q.obj (P ⊗ Q)) ⟶ r.obj (f.obj (P ⊗ Q)) := k.hom.app (P ⊗ Q)
  change _ = g.map (Functor.LaxMonoidal.μ q P Q) ≫ b ≫ 𝟙 _
  rw [CategoryTheory.Category.comp_id]

end MonoidalSquare

section Abstract

universe a b
variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  (F : A ⥤ B) [F.Additive] [F.Monoidal] [F.IsEquivalence]

private local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
private local instance : HasColimitsOfSize.{0, 0} B := hasColimitsOfSizeShrink B
private local instance (P Q : GradedObject ℤ A) : P.HasTensor Q := inferInstance
private local instance (P Q : GradedObject ℤ B) : P.HasTensor Q := inferInstance

end Abstract

attribute [local instance 1000001] sectionRingHasSheafCompose
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

section NormalizationUncurry
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃
variable {C₀ : Type u₀} [Category.{v₀} C₀] {D₀ : Type u₁} [Category.{v₁} D₀]
  {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
  {D : Type u₃} [Category.{v₃} D]
  {qC : C₀ ⥤ C} {qD : D₀ ⥤ D} {f₀ : C₀ ⥤ D₀} {f : C ⥤ D}
  {factor : qC ⋙ f ≅ f₀ ⋙ qD}
  {t₀ : C₀ × C₀ ⥤ C₀} {s : D × D ⥤ D} {s₀ : D₀ × D₀ ⥤ D₀}
  {μ : ∀ P Q : C₀,
    (MonoidalCategory.tensor C).obj (qC.obj P, qC.obj Q) ⟶ qC.obj (t₀.obj (P, Q))}
  {c₀ : ∀ P Q : C₀, f₀.obj (t₀.obj (P, Q)) ≅ s₀.obj (f₀.obj P, f₀.obj Q)}
  {flat : D₀ → Prop}
  {model : ∀ (P Q : D₀), flat P → flat Q →
    (qD.obj (s₀.obj (P, Q)) ≅ s.obj (qD.obj P, qD.obj Q))}
  {c : MonoidalCategory.tensor C ⋙ f ≅ (f.prod f) ⋙ s}

end NormalizationUncurry

section Ringed

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

private local instance ringedMonoidal : MonoidalCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.moduleMonoidal.{u + 1, u, u} J R
private local instance ringedSymmetric : SymmetricCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.moduleSymmetric.{u + 1, u, u} J R
private local instance ringedPreadditive : MonoidalPreadditive (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.modulePreadditive.{u + 1, u, u} J R
private local instance ringedClosed : MonoidalClosed (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.moduleClosed.{u + 1, u, u} J R
private local instance ringedGrothendieck : IsGrothendieckAbelian.{u + 1}
    (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.moduleGrothendieck.{u + 1, u, u} J R
private local instance ringedFlat : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  RingedDerivedNative.moduleFlat.{u + 1, u, u} J R

private local instance ringedComplexTensor
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ) :
    P.HasTensor Q := inferInstance

variable {A : Type*} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  (F : A ⥤ SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  [F.Additive] [F.IsEquivalence] [fMonoidal : F.Monoidal]

private local instance sourceComplexTensor (P Q : CochainComplex A ℤ) :
    P.HasTensor Q := inferInstance

variable
  (raw : ∀ P Q : CochainComplex A ℤ,
    (F.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} J R).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P,
          (F.mapHomologicalComplex (.up ℤ)).obj Q))
  (hraw : ∀ (P Q : CochainComplex A ℤ) (p q n : ℤ) (h : p + q = n),
    F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (raw P Q).hom.f n =
      Functor.OplaxMonoidal.δ F (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)

private def ringedSquare
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      J R))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1} J R S)
    (c : MonoidalCategory.tensor
          (DerivedCategory A) ⋙
          F.mapDerivedCategory ≅
        (F.mapDerivedCategory.prod
          F.mapDerivedCategory) ⋙ S.tensor) : Prop :=
  tensorLocalizationSquareHEq DerivedCategory.Q DerivedCategory.Q
        (F.mapHomologicalComplex (.up ℤ))
        F.mapDerivedCategory
        F.mapDerivedCategoryFactors
        (MonoidalCategory.tensor _) (MonoidalCategory.tensor _) S.tensor
        (coefficientTotalTensor.{u, u + 1, u} J R)
        (Functor.LaxMonoidal.μ DerivedCategory.Q)
        raw
        (CochainComplex.IsKFlatIndependentCoefficients
          (J := J) (R := R))
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 1} J R S T) c

end Ringed

attribute [local implicit_reducible] ringedMonoidal RingedDerivedNative.moduleMonoidal
  SheafOfModules.cochainModulesMonoidal ringedSymmetric RingedDerivedNative.moduleSymmetric
  SheafOfModules.cochainModulesSymmetric

attribute [local instance 30000] ringedComplexTensor

attribute [local implicit_reducible] Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local implicit_reducible] CategoryTheory.Mod.monoidalCategoryCochainComplex
  CategoryTheory.Mod.derivedMonoidalCategory CategoryTheory.Mod.laxMonoidalQ
  internalComplexMonoidal sliceCochainMonoidal

section Generic
set_option backward.isDefEq.respectTransparency true

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [(J.W (A := AddCommGrpCat.{u + 1})).IsMonoidal]

attribute [local instance 30001] Sheaf.monoidalCategory
attribute [local instance 30002] Sheaf.symmetricCategory
attribute [local instance 30000] sectionComparisonBraiding

variable
  (R : Sheaf J AddCommGrpCat.{u + 1}) [MonObj R] [hcomm : IsCommMonObj R]

private local instance directComm :
    @IsCommMonObj (Sheaf J AddCommGrpCat.{u + 1}) _ _
      (Sheaf.braidedCategory J AddCommGrpCat.{u + 1}) R _ := by
  exact hcomm

private local instance symmetricComm :
    @IsCommMonObj (Sheaf J AddCommGrpCat.{u + 1}) _ _
      (Sheaf.symmetricCategory J AddCommGrpCat.{u + 1}).toBraidedCategory R _ := by
  exact hcomm

open CategoryTheory.InternalAbelianSheafModule

attribute [local irreducible] sectionModuleFunctor
attribute [local implicit_reducible] sectionModuleEquivalence

attribute [local irreducible] comparison_tensorIso comparison_unitIso

private local instance sectionFunctorAdditive :
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).Additive :=
  comparison_EAdditive J R

private local instance sectionFunctorEquivalence :
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).IsEquivalence :=
  comparison_EEquiv J R

private def SectionMonoidalData :=
  OrdinaryMonoidalData _ (comparison_tensorIso J R)

private theorem section_monoidal_data : Nonempty (SectionMonoidalData.{u} J R) := by
  exact ordinary_monoidal_data _ (comparison_tensorIso J R) (comparison_unitIso J R)
    (comparison_tensorIso_natural J R) (comparison_tensorIso_assoc J R)
    (comparison_tensorIso_leftUnitor J R) (comparison_tensorIso_rightUnitor J R)

variable
  [sourceClosed : MonoidalClosed (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceGroth : IsGrothendieckAbelian.{u + 1} (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceFlat : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]

private local instance internalComplexTensor
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ) :
    P.HasMapBifunctor Q (curriedTensor _) :=
  InternalAbelianSheafModule.comparison_internalTotalExists J R P Q

end Generic

open CategoryTheory.InternalAbelianSheafModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

attribute [local irreducible] CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor

attribute [local implicit_reducible] hom complexForward internalTotalTensor sliceForward
  sliceComplexForward sliceLocalizationIso sliceLocalizationTensorMap sliceNativeTensor

attribute [local irreducible] sliceEquivalence sliceRingObject
attribute [local instance] ringedMonoidal ringedSymmetric ringedPreadditive
  ringedClosed ringedGrothendieck ringedFlat

attribute [local instance] sectionFunctorAdditive sectionFunctorEquivalence
attribute [local implicit_reducible] sectionModuleEquivalence

set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
