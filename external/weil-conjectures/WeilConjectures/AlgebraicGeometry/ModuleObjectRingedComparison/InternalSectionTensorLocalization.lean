/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSliceDerivedHomComparison
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization

/-! # Localization of the sectionwise tensor comparison

## References

* Stacks 03CV, 03EK, 06YL, 06YS and 08J9
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

private theorem total_eq_native (P Q : CochainComplex A ℤ)
    (c : (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj Q)
    (hc : ∀ (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ c.hom.f n =
        Functor.OplaxMonoidal.δ F (P.X p) (Q.X q) ≫
          HomologicalComplex.ιTensorObj
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) :
    c = (F.mapCochainComplexμIso P Q).symm := by
  apply Iso.ext
  change c.hom = (F.mapCochainComplexμIso P Q).inv
  rw [Functor.mapCochainComplexμIso_inv]
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map F
  intro p q h
  rw [hc]
  exact (HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (Functor.OplaxMonoidal.δNatTrans F) (.up ℤ) P Q p q n h).symm

private structure NativeDescentData where
  iso : MonoidalCategory.tensor (DerivedCategory A) ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ MonoidalCategory.tensor (DerivedCategory B)
  square : ∀ P Q : CochainComplex A ℤ,
    iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
        F.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map (F.mapCochainComplexμIso P Q).inv

private theorem NativeDescentData.normalized_with (d : NativeDescentData F)
    (P Q : CochainComplex A ℤ)
    (c : (F.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (F.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (F.mapHomologicalComplex (.up ℤ)).obj Q)
    (hc : c = (F.mapCochainComplexμIso P Q).symm)
    [IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q))] :
    d.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
        F.mapDerivedCategoryFactors.hom.app Q) =
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
      DerivedCategory.Q.map c.hom ≫
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q)) := by
  rw [hc]
  apply (cancel_mono (Functor.LaxMonoidal.μ DerivedCategory.Q
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q))).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact d.square P Q

private theorem nativeDescent : Nonempty (NativeDescentData F) := by
  obtain ⟨d⟩ := ExactMonoidalEquivalenceDerived.left_data F
  let := d.homotopyMonoidal
  let := d.derivedMonoidal
  have := d.homotopyFactors
  have := d.derivedFactors
  have := ExactMonoidalEquivalenceDerived.derivedFactors_monoidal F
  let c : MonoidalCategory.tensor (DerivedCategory A) ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙
        MonoidalCategory.tensor (DerivedCategory B) :=
    NatIso.ofComponents
      (fun p ↦ (Functor.Monoidal.μIso F.mapDerivedCategory p.1 p.2).symm)
      (fun f ↦ (Functor.OplaxMonoidal.δ_natural F.mapDerivedCategory f.1 f.2).symm)
  refine ⟨⟨c, ?_⟩⟩
  intro P Q
  have h := monoidal_square DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory F.mapDerivedCategoryFactors P Q
  exact h

end Abstract

attribute [local instance 1000001] sectionRingHasSheafCompose
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

private def uncurryComparison {D E : Type*} [Category D] [Category E]
    [MonoidalCategory D] {F : D ⥤ E} {G : D × D ⥤ E}
    (c : MonoidalCategory.tensor D ⋙ F ≅ G) :
    Functor.uncurry.obj (curriedTensor D) ⋙ F ≅ G :=
  NatIso.ofComponents (fun p ↦ c.app p) (fun f ↦ by
    change F.map (f.1 ▷ _ ≫ _ ◁ f.2) ≫ c.hom.app _ = c.hom.app _ ≫ G.map f
    simpa only [Functor.comp_map, MonoidalCategory.tensor_map,
      MonoidalCategory.tensorHom_def] using c.hom.naturality f)

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

private theorem uncurryComparison_square
    (h : tensorLocalizationSquareHEq qC qD f₀ f factor (MonoidalCategory.tensor C)
      t₀ s s₀ μ c₀ flat model c) :
    tensorLocalizationSquareHEq qC qD f₀ f factor
      (Functor.uncurry.obj (curriedTensor C)) t₀ s s₀ μ c₀ flat model
      (uncurryComparison c) := by
  intro P Q hP hQ
  exact h P Q hP hQ
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

private structure ClosedComparisonData
    {S : Type*} (M : S → Type*) (I : S → Type*)
    (N : ∀ s (_m : M s), I s → Prop) where
  closed : S
  models : M closed
  iso : I closed
  square : N closed models iso

private theorem ClosedComparisonData.to_exists
    {S : Type*} {M : S → Type*} {I : S → Type*}
    {N : ∀ s (_m : M s), I s → Prop} {K : ∀ s, M s → Type*}
    (mk : ∀ s m i, N s m i → K s m)
    (h : Nonempty (ClosedComparisonData M I N)) : ∃ s m, Nonempty (K s m) := by
  obtain ⟨d⟩ := h
  exact ⟨d.closed, d.models, ⟨mk _ _ d.iso d.square⟩⟩

private abbrev RingedNormalizationData :=
  ClosedComparisonData
    (CoefficientTensorModels.{u, u + 1, u, u + 1} J R)
    (fun S ↦ MonoidalCategory.tensor (DerivedCategory A) ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S.tensor)
    (ringedSquare J R F raw)

include hraw in
private theorem ringed_normalized : Nonempty (RingedNormalizationData J R F raw) := by
  obtain ⟨d⟩ := nativeDescent F
  obtain ⟨S, hS, T, hT⟩ := RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 1}
    J R
  rcases S with ⟨ss, adj, hn⟩
  dsimp only at hS
  subst ss
  refine ⟨⟨⟨_, adj, hn⟩, T, d.iso, ?_⟩⟩
  intro P Q hP hQ
  dsimp only [CoefficientTensorModels.iso]
  rw [eq_of_heq hT]
  have := RingedDerivedNative.isIso_mu.{u + 1, u, u, u + 1} J R
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q)
    (Or.inl hP)
  apply heq_of_eq
  exact NativeDescentData.normalized_with F d P Q (raw P Q)
    (total_eq_native F P Q (raw P Q) (hraw P Q))

include hraw in
private theorem ringed_normalized_transport
    (B : Sheaf J CommRingCat.{u + 1}) (e : R = B)
    (E : A ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))
    [E.Additive] [E.IsEquivalence] (he : HEq E F)
    (t : ∀ P Q : CochainComplex A ℤ,
      (E.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (coefficientTotalTensor.{u, u + 1, u} J B).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P,
            (E.mapHomologicalComplex (.up ℤ)).obj Q))
    (ht : ∀ P Q, HEq (t P Q) (raw P Q)) :
    Nonempty (RingedNormalizationData J B E t) := by
  subst B
  have hE : E = F := eq_of_heq he
  subst E
  have hh : t = raw := by
    funext P Q
    exact eq_of_heq (ht P Q)
  subst t
  exact ringed_normalized J R F raw hraw

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

private theorem canonicalOrdinaryForSite_eq_comparison
    (M N : Mod (Sheaf J AddCommGrpCat.{u + 1}) R) :
    ordinaryTensorIsoForSite J R M N = comparison_tensorIso J R M N := by
  unfold ordinaryTensorIsoForSite comparison_tensorIso
  rfl

variable
  [sourceClosed : MonoidalClosed (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceGroth : IsGrothendieckAbelian.{u + 1} (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]
  [sourceFlat : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf J AddCommGrpCat.{u + 1}) R)]

private local instance internalComplexTensor
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ) :
    P.HasMapBifunctor Q (curriedTensor _) :=
  InternalAbelianSheafModule.comparison_internalTotalExists J R P Q

private theorem ordinary_raw_summand (m : SectionMonoidalData.{u} J R)
    (P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    let := m.monoidal
    (sectionModuleFunctor.{u + 1, u + 1, u} J R).map
      (HomologicalComplex.ιTensorObj P Q p q n h) ≫
        (ordinaryComplexTensorIsoForSite J R P Q).hom.f n =
      Functor.OplaxMonoidal.δ
        (sectionModuleFunctor.{u + 1, u + 1, u} J R) (P.X p) (Q.X q) ≫
        HomologicalComplex.ιTensorObj
          (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex
            (.up ℤ)).obj P)
          (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex
            (.up ℤ)).obj Q) p q n h := by
  let := m.monoidal
  have hd := m.delta (P.X p) (Q.X q)
  rw [← canonicalOrdinaryForSite_eq_comparison] at hd
  exact (ordinaryComplexTensorIsoForSite_summand J R P Q p q n h).trans
    (congrArg (fun f ↦ f ≫ HomologicalComplex.ιTensorObj
      (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex
        (.up ℤ)).obj P)
      (((sectionModuleFunctor.{u + 1, u + 1, u} J R).mapHomologicalComplex
        (.up ℤ)).obj Q) p q n h) hd.symm)

private theorem section_normalized
    (B : Sheaf J CommRingCat.{u + 1}) (e : sectionRingSheaf.{u + 1, u + 1, u} J R = B)
    (E : Mod (Sheaf J AddCommGrpCat.{u + 1}) R ⥤ SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))
    [E.Additive] [E.IsEquivalence]
    (he : HEq E (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor)
    (t : ∀ P Q : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) ℤ,
      (E.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (coefficientTotalTensor.{u, u + 1, u} J B).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P,
            (E.mapHomologicalComplex (.up ℤ)).obj Q))
    (ht : ∀ P Q, HEq (t P Q) (ordinaryComplexTensorIsoForSite J R P Q)) :
    Nonempty (@RingedNormalizationData.{u, u + 2} C inferInstance J inferInstance inferInstance B
      (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) inferInstance inferInstance sourceGroth
      inferInstance sourceClosed inferInstance inferInstance sourceFlat E inferInstance
      inferInstance t) := by
  obtain ⟨m⟩ := section_monoidal_data J R
  let := m.monoidal
  exact @ringed_normalized_transport.{u, u + 2} C inferInstance J inferInstance
    inferInstance (sectionRingSheaf.{u + 1, u + 1, u} J R)
    (Mod (Sheaf J AddCommGrpCat.{u + 1}) R) inferInstance inferInstance sourceGroth
    inferInstance sourceClosed inferInstance inferInstance sourceFlat
    (sectionModuleFunctor.{u + 1, u + 1, u} J R) inferInstance inferInstance
    m.monoidal (ordinaryComplexTensorIsoForSite J R)
    (ordinary_raw_summand J R m) B e E inferInstance inferInstance he t ht

end Generic

open CategoryTheory.InternalAbelianSheafModule

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

attribute [local irreducible] complexTensorIso totalComparison ordinaryTensorIso
  CategoryTheory.InternalAbelianSheafModule.sectionModuleFunctor

attribute [local implicit_reducible] hom forward localizationIso localizationTensorMap
  complexForward internalTotalTensor sliceDerivedForward sliceComplexForward
  sliceDerivedLocalizationIso sliceLocalizationTensorMap sliceNativeTensor

attribute [local irreducible] sliceEquivalence sliceRingObject
attribute [local instance] ringedMonoidal ringedSymmetric ringedPreadditive
  ringedClosed ringedGrothendieck ringedFlat

attribute [local instance] sectionFunctorAdditive sectionFunctorEquivalence
attribute [local implicit_reducible] sectionModuleEquivalence

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
/-- The section equivalence identifies the native derived tensors with the ringed
closed tensor, with the prescribed K-flat representative squares, globally and on
all localized sites. This statement contains no comparison of internal Homs. -/
theorem internalSection_tensorLocalization :
    (∃ (S : CoefficientClosedStructure (hom Λ X))
      (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) S),
      Nonempty (TensorComparison Λ X S T)) ∧
    (∀ U : X.ProEt,
      ∃ (S : CoefficientClosedStructure
          (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
            ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
        (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
          ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) S),
        Nonempty (SliceTensorComparison Λ X U S T)) := by
  constructor
  · have hcomm := (inferInstance : IsCommMonObj (condensedRingObj Λ X))
    let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
      (Sheaf.symmetricCategory (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).toBraidedCategory
    have : IsCommMonObj (condensedRingObj Λ X) := hcomm
    have : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
    have : (Scheme.ProEt.topology X).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := inferInstance
    have : ((Scheme.ProEt.topology X).W (A := AddCommGrpCat.{u + 1})).IsMonoidal :=
      inferInstance
    let : MonoidalClosed (Internal Λ X) := CategoryTheory.Mod.monoidalClosed
    have : IsGrothendieckAbelian.{u + 1} (Internal Λ X) := inferInstance
    have : Abelian.HasFunctorialFlatResolution (Internal Λ X) := inferInstance
    have ht (P Q : CochainComplex (Internal Λ X) ℤ) :
        HEq (totalComparison Λ X P Q)
          (ordinaryComplexTensorIsoForSite (Scheme.ProEt.topology X)
            (condensedRingObj Λ X) P Q) :=
      totalComparison_heq Λ X P Q
    let h := section_normalized.{u} (Scheme.ProEt.topology X) (condensedRingObj Λ X)
      (ring Λ X) rfl (sectionForward Λ X)
      (heq_of_eq (sectionForward_eq Λ X)) (totalComparison Λ X) ht
    refine ClosedComparisonData.to_exists
      (K := fun S T ↦ TensorComparison Λ X S T) ?_ h
    intro S T c hc
    exact ⟨uncurryComparison c, uncurryComparison_square hc⟩
  · intro U
    have : HasSheafify ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
      inferInstance
    have : ((Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := inferInstance
    have : (((Scheme.ProEt.topology X).over U).W (A := AddCommGrpCat.{u + 1})).IsMonoidal :=
      inferInstance
    have : IsGrothendieckAbelian.{u + 1} (SliceInternal Λ X U) := inferInstance
    have hcomm := sliceRingComm Λ X U
    let : BraidedCategory
        (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) :=
      (Sheaf.symmetricCategory ((Scheme.ProEt.topology X).over U)
        AddCommGrpCat.{u + 1}).toBraidedCategory
    have : IsCommMonObj (sliceRingObject Λ X U) := hcomm
    let : SymmetricCategory
        (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) :=
      Sheaf.symmetricCategory ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}
    let : MonoidalClosed
        (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) :=
      GrothendieckTopology.monoidalClosed_sheaf_of_essentiallySmall
        AddCommGrpCat.{u + 1} ((Scheme.ProEt.topology X).over U)
    let : MonoidalClosed (SliceInternal Λ X U) := CategoryTheory.Mod.monoidalClosed
    have : Abelian.HasFunctorialFlatResolution
        (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) :=
      GrothendieckTopology.hasFunctorialFlatResolution_sheaf_of_essentiallySmall
        AddCommGrpCat.{u + 1} ((Scheme.ProEt.topology X).over U)
    have : Abelian.HasFunctorialFlatResolution (SliceInternal Λ X U) :=
      CategoryTheory.Mod.hasFunctorialFlatResolution
    have he : HEq (sliceEquivalence Λ X U).functor
        (sectionModuleEquivalence.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
          (sliceRingObject Λ X U)).functor := by
      exact sliceEquivalence_functor_heq Λ X U
    have ht (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
        HEq (sliceTotalComparison Λ X U P Q)
          (ordinaryComplexTensorIsoForSite ((Scheme.ProEt.topology X).over U)
            (sliceRingObject Λ X U) P Q) := by
      exact sliceTotalComparison_heq Λ X U P Q
    let h := section_normalized.{u} ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U)
      ((ring Λ X).over U) (sliceSectionRing_eq Λ X U)
      (sliceEquivalence Λ X U).functor he (sliceTotalComparison Λ X U) ht
    refine ClosedComparisonData.to_exists
      (K := fun S T ↦ SliceTensorComparison Λ X U S T) ?_ h
    intro S T c hc
    exact ⟨c, hc⟩
end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
