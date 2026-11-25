/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Canonical normalized scalar tensor

## References

* Stacks 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
private noncomputable abbrev cachedComplexMonoidal :
    MonoidalCategory (CochainComplex C ℤ) := inferInstance
private noncomputable abbrev cachedHomotopyMonoidal :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private noncomputable abbrev cachedDerivedMonoidal :
    MonoidalCategory (DerivedCategory C) := inferInstance
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

private theorem tensorator_Q_generic
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ Q) := by
  unfold Functor.LaxMonoidal.μ
  unfold DerivedCategory.laxMonoidalQ
  unfold inferInstance
  unfold DerivedCategory.instLaxMonoidalQ
  unfold Functor.LaxMonoidal.ofIso
  dsimp only
  rw [Functor.LaxMonoidal.comp_μ]
  change (_ ⊗ₘ _) ≫ (_ ≫ (DerivedCategory.Qh (C := C)).map (𝟙 _)) ≫ _ = _
  rw [(DerivedCategory.Qh (C := C)).map_id, Category.comp_id]
  rfl

private theorem tensorator_Q_strict {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj P)
        ((HomotopyCategory.quotient _ _).obj Q) := by
  rw [tensorator_Q_generic]
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ _ ≫ 𝟙 _ = _
  simp only [id_tensorHom_id, Category.id_comp, Category.comp_id]

private theorem cochain_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj (P ⊗ Q)) ≫
      DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  erw [tensorator_Q_strict ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q),
    tensorator_Q_strict P Q]
  let δ := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q
  have hδ := DerivedCategory.quotientCompQhIso_hom_naturality δ
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map δ) ≫ 𝟙 _ =
    𝟙 _ ≫ DerivedCategory.Q.map δ at hδ
  simp only [Category.comp_id, Category.id_comp] at hδ
  have h := G.leftDerivedTensorComparison_app_app_comp_tensorHom
    ((HomotopyCategory.quotient _ _).obj P) ((HomotopyCategory.quotient _ _).obj Q)
  rw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app] at h
  rw [hδ] at h
  exact h

private def cochainCompute
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalPreadditive C₁] [MonoidalClosed C₁]
    [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    (P : CochainComplex C₁ ℤ) :
    G.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P) :=
  G.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C₁).inv.app P) ≫
    G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso C₂).hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj P)

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

set_option backward.defeqAttrib.useBackward true
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  CategoryTheory.Sheaf.symmetricCategory CategoryTheory.Sheaf.braidedCategory

/-- The existing sheaf symmetry with its native braiding retained explicitly. -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarSheafSymmetric
    (T : AlgebraicGeometry.Scheme.{u}) :
    SymmetricCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  { toBraidedCategory := AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} T
    symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
      (AlgebraicGeometry.ProEtale.sheafSymmetricCategory T) M N }

attribute [local instance 21000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarSheafSymmetric

/-- The existing closed structure on internal modules, with structural arguments shared. -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleClosed
    (B : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalClosed (AlgebraicGeometry.ProEtale.QuotientChange.Modules B T) := inferInstance

/-- The existing braiding on internal modules, with the ambient sheaf structure shared. -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleBraided
    (B : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (T : AlgebraicGeometry.Scheme.{u}) :
    BraidedCategory (AlgebraicGeometry.ProEtale.QuotientChange.Modules B T) := inferInstance

/-- The existing functorial flat resolutions of internal modules. -/
theorem AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleFlat
    (B : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (T : AlgebraicGeometry.Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (AlgebraicGeometry.ProEtale.QuotientChange.Modules B T) := inferInstance

/-- Scalar extension preserves quasi-isomorphisms between K-flat complexes. -/
theorem AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarPreservesKFlat
    {B B' : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj B] [IsCommMonObj B] [MonObj B'] [IsCommMonObj B']
    (a : B ⟶ B') [IsMonHom a] (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.ProEtale.QuotientChange.extension a T).PreservesKFlatQuasiIso :=
  CategoryTheory.Mod.preservesKFlatQuasiIso _

attribute [local instance 2000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleClosed
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleBraided
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleFlat
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarPreservesKFlat

attribute [local irreducible] cochainCompute

private theorem cochainCompute_eq
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalPreadditive C₁] [MonoidalClosed C₁]
    [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    (P : CochainComplex C₁ ℤ) :
    cochainCompute.{u} G P =
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) := by
  unfold cochainCompute
  change G.leftDerivedFunctor.map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  rw [G.leftDerivedFunctor.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]

private theorem cochainCompute_tensor_comparison
    {C₁ C₂ : Type*} [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Abelian C₁] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₁] [IsGrothendieckAbelian.{u + 1} C₂]
    [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalPreadditive C₁] [MonoidalPreadditive C₂]
    [MonoidalClosed C₁] [MonoidalClosed C₂] [BraidedCategory C₁] [BraidedCategory C₂]
    [Abelian.HasFunctorialFlatResolution C₁] [Abelian.HasFunctorialFlatResolution C₂]
    (G : C₁ ⥤ C₂) [G.Additive] [G.PreservesKFlatQuasiIso]
    [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
    (P Q : CochainComplex C₁ ℤ) :
    ((G.leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)) ≫
      (cochainCompute.{u} G P ⊗ₘ cochainCompute.{u} G Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) =
    G.leftDerivedFunctor.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      cochainCompute.{u} G (P ⊗ Q) ≫ DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app P).app Q) := by
  have h := cochain_tensor_comparison.{u} G P Q
  have ht : cochainCompute.{u} G P ⊗ₘ cochainCompute.{u} G Q =
      G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj P) ⊗ₘ
        G.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Q) :=
    congrArg₂ (fun p q ↦ p ⊗ₘ q) (cochainCompute_eq.{u} G P) (cochainCompute_eq.{u} G Q)
  have hr := cochainCompute_eq.{u} G (P ⊗ Q)
  convert h using 1
  · congr 2
  · congr 1
    congr 1

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

/-- Uncurry a tensor comparison isomorphism without changing any components. -/
def uncurryTensorIso
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    (G : C₁ ⥤ C₂) (T₁ : C₁ ⥤ C₁ ⥤ C₁) (T₂ : C₂ ⥤ C₂ ⥤ C₂)
    (b : (Functor.postcompose₂.obj G).obj T₁ ≅
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj T₂) :
    Functor.uncurry.obj T₁ ⋙ G ≅ (G.prod G) ⋙ Functor.uncurry.obj T₂ :=
  NatIso.ofComponents (fun Z ↦ (b.app Z.1).app Z.2) (by
    rintro ⟨U, V⟩ ⟨U', V'⟩ ⟨g, h⟩
    have h₁ := NatTrans.congr_app (b.hom.naturality g) V
    have h₂ := (b.hom.app U').naturality h
    dsimp at h₁ h₂ ⊢
    rw [Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁])

/-- The actual bifunctor-derived scalar tensorator, uncurried to pairs. -/
@[irreducible] def canonicalTensor (T : Scheme.{u}) : TensorIso a T := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  let := scalarModuleFlat Λ T
  let := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  unfold TensorIso D CondensedRing.derivedTensor
  have := CondensedRing.internalScalar_preservesFlat a T
  let δ := (extension a T).leftDerivedTensorComparison
  have hδ : IsIso δ := (extension a T).isIso_leftDerivedTensorComparison
  exact uncurryTensorIso _ _ _ (@asIso _ _ _ _ δ hδ)

/-- The canonical derived scalar tensorator has the specified cochain counit square. -/
theorem canonicalTensor_normalized (T : Scheme.{u}) :
    TensorNormalized a T (canonicalTensor a T) := by
  intro P Q _ _ _ _
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  let := scalarModuleFlat Λ T
  let := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  have h := cochainCompute_tensor_comparison.{u} (extension a T) P Q
  unfold cochainCompute at h
  unfold canonicalTensor compute scalarCounit D totalScalar
  dsimp only [uncurryTensorIso, NatIso.ofComponents_hom_app, Iso.app_hom, asIso_hom]
  convert h using 1 <;> rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
