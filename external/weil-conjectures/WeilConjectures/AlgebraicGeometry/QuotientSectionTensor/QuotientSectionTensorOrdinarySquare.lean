/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import all WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
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
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Ordinary scalar section tensor square

## References

* Stacks, Cohomology on Sites, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
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

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem scalar_tensor_ext (T : Scheme.{u})
    (M N : ModuleRingedComparison.internalModules Λ T)
    (W : ModuleRingedComparison.modules Λ' T)
    (f g : (ModuleRingedComparison.equivalence Λ' T).functor.obj
      ((Mod.extendScalars (ProEtale.coefficientMap a T)).obj (M ⊗ N)) ⟶ W)
    (h : ∀ (V : T.ProEtᵒᵖ) (s : (ModuleRingedComparison.ring Λ' T).obj.obj V)
      (x : M.X.obj.obj V) (y : N.X.obj.obj V),
      f.val.app V (InternalAbelianSheafModule.internalScalarGenerator
        (Scheme.ProEt.topology T) (ProEtale.coefficientMap a T) (M ⊗ N) V s
          (ModuleRingedComparison.internalPureTensor Λ T M N V x y)) =
      g.val.app V (InternalAbelianSheafModule.internalScalarGenerator
        (Scheme.ProEt.topology T) (ProEtale.coefficientMap a T) (M ⊗ N) V s
          (ModuleRingedComparison.internalPureTensor Λ T M N V x y))) : f = g := by
  let J := Scheme.ProEt.topology T
  let ES := sheafToPresheaf J Ab.{u + 1}
  apply (SheafOfModules.toSheaf _).map_injective
  apply (cancel_epi (Mod.extendπ (ProEtale.coefficientMap a T) (M ⊗ N))).mp
  apply (cancel_epi ((condensedRingObj Λ' T) ◁ Mod.tensorObjπ M N)).mp
  apply Sheaf.tensor_hom_ext
  apply ((J.W.whiskerLeft_mem (condensedRingObj Λ' T).obj _
    (InternalAbelianSheafModule.comparison_sheafTensor_mem J M.X N.X))
    (SheafOfModules.toSheaf _ |>.obj W).obj
    (SheafOfModules.toSheaf _ |>.obj W).property).injective
  simp only [Functor.map_comp]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc]
  ext V t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul s t =>
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul x y => exact h V s x y

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)] in
private theorem internal_delta_unit (T : Scheme.{u})
    (M N : ModuleRingedComparison.internalModules Λ T)
    (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V) :
    let := CondensedRing.internalScalarMonoidal a T
    (((ModuleRingedComparison.equivalence Λ' T).functor.map
      (Functor.OplaxMonoidal.δ (Mod.extendScalars (ProEtale.coefficientMap a T)) M N)).val.app V)
      ((Mod.extendUnitHom (ProEtale.coefficientMap a T) (M ⊗ N)).hom.app V
        (ModuleRingedComparison.internalPureTensor Λ T M N V x y)) =
    ModuleRingedComparison.internalPureTensor Λ' T _ _ V
      ((Mod.extendUnitHom (ProEtale.coefficientMap a T) M).hom.app V x)
      ((Mod.extendUnitHom (ProEtale.coefficientMap a T) N).hom.app V y) := by
  let := CondensedRing.internalScalarMonoidal a T
  have hn := (CondensedRing.internalScalarMonoidalNormalized_existsUnique a T).exists.choose_spec
    M N
  let F := sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  have hh := congrArg (fun k ↦ Functor.LaxMonoidal.μ F M.X N.X ≫ F.map k) hn
  simp only [Functor.map_comp] at hh
  rw [← Functor.LaxMonoidal.μ_natural_assoc] at hh
  exact congrArg (fun k ↦ (k.app V) (x ⊗ₜ[ℤ] y)) hh

private theorem scalar_element_eq (T : Scheme.{u}) (c : ScalarSectionData a T)
    (M : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
    (s : (ring Λ' T).obj.obj W) :
    sectionScalarElement a T c M W m s =
      (eqToHom (c.model.obj_eq M).symm).val.app W
        (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) M W m s) := by
  unfold sectionScalarElement
  apply congrArg ((eqToHom (c.model.obj_eq M).symm).val.app W)
  symm
  unfold SheafOfModules.scalarExtensionConstraintTmul
  let RS : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ' T)
  have hs := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (C := T.ProEt) (J := Scheme.ProEt.topology T) (R := RS) (𝟙 RS.obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (sectionQuotient a T) M)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app hs W) _

private theorem scalar_element_natural (T : Scheme.{u}) (c : ScalarSectionData a T)
    {M N : modules Λ T} (f : M ⟶ N) (W : T.ProEtᵒᵖ)
    (s : (ring Λ' T).obj.obj W) (m : M.val.obj W) :
    (c.model.E.map f).val.app W (sectionScalarElement a T c M W m s) =
      sectionScalarElement a T c N W (f.val.app W m) s := by
  rw [scalar_element_eq, scalar_element_eq, c.model.map_eq]
  have he := congrArg (fun k ↦ k.val.app W
    (SheafOfModules.scalarExtensionConstraintTmul (sectionQuotient a T) M W m s))
      ((eqToIso (c.model.obj_eq M)).inv_hom_id)
  change (eqToHom (c.model.obj_eq M)).val.app W
    ((eqToHom (c.model.obj_eq M).symm).val.app W _) = _ at he
  change (eqToHom (c.model.obj_eq N).symm).val.app W
    ((SheafOfModules.changeOfRingsHom (sectionQuotient a T) M f).val.app W
      ((eqToHom (c.model.obj_eq M)).val.app W
        ((eqToHom (c.model.obj_eq M).symm).val.app W _))) = _
  rw [he]
  exact congrArg ((eqToHom (c.model.obj_eq N).symm).val.app W)
    (SheafOfModules.extension_map_tmul (sectionQuotient a T) f W m s)

private theorem scalar_unit_image (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W) :
    (c.ordinary.hom.app M).val.app W
      (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
    sectionScalarElement a T c ((equivalence Λ T).functor.obj M) W m 1 := by
  have h := congrArg ((eqToHom (c.model.obj_eq _).symm).val.app W) (hc.1 M W m)
  have hi := congrArg (fun k ↦ k.val.app W
    ((c.ordinary.hom.app M).val.app W
      (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m)))
      ((eqToIso (c.model.obj_eq _)).hom_inv_id)
  exact hi.symm.trans h

attribute [local irreducible] ordinaryTensorComparison Mod.extendRestrictAdjunction
  sectionScalarElement Mod.extendScalarsObj

-- Compare the concrete scalar-unit formulas through the section equivalence.
/-- The scalar section comparison intertwines the ordinary tensor constraints.
Compare maps after the scalar and tensor coequalizer projections. Linearity reduces
this to scalar-unit pure tensors, where the internal monoidal normalization and
the two section normalization formulas agree by naturality of the tensor pairing. -/
theorem section_tensor_ordinary_scalar_square (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
      (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
        (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
        (sectionScalarElement a T c (M ⊗ N) W (sectionPureTensor Λ T M N W m n) s) =
      sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
        (sectionScalarElement a T c M W m 1) (sectionScalarElement a T c N W n s))
    (M N : Modules Λ T) :
    let := CondensedRing.internalScalarMonoidal a T
    (equivalence Λ' T).functor.map (Functor.OplaxMonoidal.δ (extension a T) M N) ≫
      (ordinaryTensorComparison Λ' T _ _).hom ≫
      (c.ordinary.hom.app M ⊗ₘ c.ordinary.hom.app N) =
    c.ordinary.hom.app (M ⊗ N) ≫
      c.model.E.map (ordinaryTensorComparison Λ T M N).hom ≫
      (e.app ((equivalence Λ T).functor.obj M)).app
        ((equivalence Λ T).functor.obj N) := by
  let := CondensedRing.internalScalarMonoidal a T
  apply scalar_tensor_ext a T M N
  intro W s x y
  let J := Scheme.ProEt.topology T
  let A := ProEtale.coefficientMap a T
  let F := extension a T
  let ER := (equivalence Λ T).functor
  let ES := (equivalence Λ' T).functor
  let δ := Functor.OplaxMonoidal.δ F M N
  let eR := ordinaryTensorComparison Λ T M N
  let eS := ordinaryTensorComparison Λ' T (F.obj M) (F.obj N)
  simp only [InternalAbelianSheafModule.internalScalarGenerator_eq_smul,
    map_smul, Mod.extendRestrictAdjunction_unit_app_hom]
  have hg := scalar_unit_image a T c hc (M ⊗ N) W (internalPureTensor Λ T M N W x y)
  have hn := scalar_element_natural a T c eR.hom W 1 (internalPureTensor Λ T M N W x y)
  have hr := pullTensor_tensorComparison_apply Λ T M N W x y
  have hm := he (ER.obj M) (ER.obj N) W x y 1
  have hδ := internal_delta_unit a T M N W x y
  let ux := (Mod.extendUnitHom A M).hom.app W x
  let uy := (Mod.extendUnitHom A N).hom.app W y
  change s • (c.ordinary.hom.app M ⊗ₘ c.ordinary.hom.app N).val.app W
      (eS.hom.val.app W ((ES.map δ).val.app W
        ((Mod.extendUnitHom A (M ⊗ N)).hom.app W
          (internalPureTensor Λ T M N W x y)))) =
    s • ((e.app (ER.obj M)).app (ER.obj N)).val.app W
      ((c.model.E.map eR.hom).val.app W
        ((c.ordinary.hom.app (M ⊗ N)).val.app W
          ((Mod.extendUnitHom A (M ⊗ N)).hom.app W
            (internalPureTensor Λ T M N W x y))))
  apply congrArg (fun z ↦ s • z)
  let O := (c.ordinary.hom.app M ⊗ₘ c.ordinary.hom.app N).val.app W
  trans O (eS.hom.val.app W
    (internalPureTensor Λ' T (F.obj M) (F.obj N) W ux uy))
  · exact congrArg (fun z ↦ O (eS.hom.val.app W z)) hδ
  trans O (sectionPureTensor Λ' T (ES.obj (F.obj M)) (ES.obj (F.obj N)) W ux uy)
  · exact congrArg (fun z ↦ O z)
      (pullTensor_tensorComparison_apply Λ' T (F.obj M) (F.obj N) W ux uy)
  trans sectionPureTensor Λ' T (c.model.E.obj (ER.obj M)) (c.model.E.obj (ER.obj N)) W
    ((c.ordinary.hom.app M).val.app W ux) ((c.ordinary.hom.app N).val.app W uy)
  · exact InternalAbelianSheafModule.comparison_sectionTmul_natural J
      (condensedRingObj Λ' T) (c.ordinary.hom.app M) (c.ordinary.hom.app N) W ux uy
  trans sectionPureTensor Λ' T (c.model.E.obj (ER.obj M)) (c.model.E.obj (ER.obj N)) W
    (sectionScalarElement a T c (ER.obj M) W x 1)
    (sectionScalarElement a T c (ER.obj N) W y 1)
  · exact congrArg₂ (sectionPureTensor Λ' T (c.model.E.obj (ER.obj M))
      (c.model.E.obj (ER.obj N)) W)
      (scalar_unit_image a T c hc M W x) (scalar_unit_image a T c hc N W y)
  symm
  trans ((e.app (ER.obj M)).app (ER.obj N)).val.app W
    ((c.model.E.map eR.hom).val.app W
      (sectionScalarElement a T c (ER.obj (M ⊗ N)) W
        (internalPureTensor Λ T M N W x y) 1))
  · exact congrArg (fun z ↦ ((e.app (ER.obj M)).app (ER.obj N)).val.app W
      ((c.model.E.map eR.hom).val.app W z)) hg
  trans ((e.app (ER.obj M)).app (ER.obj N)).val.app W
    (sectionScalarElement a T c (ER.obj M ⊗ ER.obj N) W
      (eR.hom.val.app W (internalPureTensor Λ T M N W x y)) 1)
  · exact congrArg (((e.app (ER.obj M)).app (ER.obj N)).val.app W) hn
  trans ((e.app (ER.obj M)).app (ER.obj N)).val.app W
    (sectionScalarElement a T c (ER.obj M ⊗ ER.obj N) W
      (sectionPureTensor Λ T (ER.obj M) (ER.obj N) W x y) 1)
  · exact congrArg (fun z ↦ ((e.app (ER.obj M)).app (ER.obj N)).val.app W
      (sectionScalarElement a T c (ER.obj M ⊗ ER.obj N) W z 1)) hr
  exact hm

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
