/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.HomTensorDifferential
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.InternalSectionDerivedTensorComparison
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.Algebra.Ring.Ext

/-! # Module objects and derived Hom on a slice

Source: Stacks Project, Tags 03DH, 08J9 and 08JB; Step 5 of the module-object
comparison (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule CategoryTheory.MonObj WeilConjectures
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local instance 1000001] sectionRingHasSheafCompose
attribute [local instance] sectionFunctorAdditiveForSite sectionFunctorEquivalenceForSite

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)

private theorem cast_ring_apply {A B : CommRingCat.{u + 1}}
    (e : A = B) (x : A) :
    (ConcreteCategory.hom (eqToHom e)) x = cast (congrArg CommRingCat.carrier e) x := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sectionRing_over_eq {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    sectionRingSheaf (J.over U)
      ((J.overPullback AddCommGrpCat.{u + 1} U).obj R) =
      (sectionRingSheaf J R).over U := by
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.ext (fun W ↦ ?_) ?_
  · apply congrArg (fun s : CommRing (R.obj.obj ((Over.forget U).op.obj W)) ↦
      @CommRingCat.of _ s)
    refine CommRing.ext ?_ ?_
    · rfl
    funext a b
    have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (Over.forget U) AddCommGrpCat.{u + 1}
      (J.over U)
      J R R W
    have ht := ConcreteCategory.congr_hom h (a ⊗ₜ[ℤ] b)
    exact congrArg (fun x ↦ (μ[R]).hom.app ((Over.forget U).op.obj W) x) ht
  · intro V W f
    ext x
    simp only [CommRingCat.comp_apply, cast_ring_apply]
    rfl

/-- Literal restriction of the coefficient ring object, with its induced multiplication.
Source: Stacks 03DH (auxiliary; not a blueprint node). -/
def sliceRingObject :
    Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
  ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).obj
    (condensedRingObj Λ X)

/-- The functor-induced monoid structure, named with instance transparency so
native constructions can reuse it without unfolding the whole restriction functor.
Source: Stacks 03DH (auxiliary; not a blueprint node). -/
@[instance_reducible] instance sliceRingMonObj : MonObj (sliceRingObject Λ X U) :=
  ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).monObjObj _

/-- Restriction preserves commutativity of the coefficient multiplication.
Source: Stacks 03DH (auxiliary; not a blueprint node). -/
instance sliceRingComm : IsCommMonObj (sliceRingObject Λ X U) :=
  Functor.isCommMonObj_obj
    (F := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U)

/-- Module objects over the restricted ring, on the actual slice site.
Source: Stacks 03DH (auxiliary; not a blueprint node). -/
abbrev SliceInternal := Mod
  (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) (sliceRingObject Λ X U)

/-- Section rings commute with literal restriction.
Source: Stacks 03DH (auxiliary; not a blueprint node).
Proof: both underlying presheaves send V over U to B(V); their units and products
are the same sectionwise unit and product. Extensionality of ring structures and
presheaf natural transformations identifies the two bundled ring sheaves. -/
theorem sliceSectionRing_eq :
    sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U) = (ring Λ X).over U := by
  delta sliceRingObject sliceRingMonObj
  exact sectionRing_over_eq (Scheme.ProEt.topology X) U (condensedRingObj Λ X)

attribute [local irreducible] sliceRingMonObj

/-- The actual section-action equivalence for B restricted to U. Equality transport
changes only the two presentations of its section ring, retaining the functor's data.
Source: Stacks 00YV, 03DH (auxiliary; not a blueprint node). -/
def sliceEquivalence : SliceInternal Λ X U ≌ SheafOfModules.{u + 1}
    ((sheafCompose ((Scheme.ProEt.topology X).over U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((ring Λ X).over U)) :=
  Eq.mp (congrArg (fun R ↦ SliceInternal Λ X U ≌ SheafOfModules.{u + 1}
    ((sheafCompose ((Scheme.ProEt.topology X).over U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (sliceSectionRing_eq Λ X U))
    (sectionModuleEquivalence.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U))

/-- The local section equivalence is additive, including equality transport.
Source: Stacks 00YV, 03DH (auxiliary; not a blueprint node).
Proof: every equivalence of these preadditive categories preserves binary products
and zero morphisms, hence addition. This applies directly to the transported
equivalence, without unfolding its equality transport. -/
@[instance] theorem sliceEquivalence_additive :
    (sliceEquivalence Λ X U).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

attribute [local irreducible] sliceEquivalence

/-- Sectionwise modules over the literally restricted section ring.
Source: Stacks 03DH (auxiliary; not a blueprint node). -/
abbrev SliceModules := SheafOfModules.{u + 1}
  ((sheafCompose ((Scheme.ProEt.topology X).over U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((ring Λ X).over U))

/-- The direct derived section functor. Naming it avoids unfolding the equivalence
and both its coherence isomorphisms when checking representative endpoints.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def sliceForward :
    DerivedCategory (SliceInternal Λ X U) ⥤ DerivedCategory (SliceModules Λ X U) :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategory

/-- Termwise extension of the fixed local section-action equivalence.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def sliceComplexForward :
    CochainComplex (SliceInternal Λ X U) ℤ ⥤ CochainComplex (SliceModules Λ X U) ℤ :=
  (sliceEquivalence Λ X U).functor.mapHomologicalComplex (.up ℤ)

/-- The actual localization comparison for the termwise local section functor.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
def sliceLocalizationIso :
    DerivedCategory.Q ⋙ sliceForward Λ X U ≅
      sliceComplexForward Λ X U ⋙ DerivedCategory.Q :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategoryFactors

set_option backward.isDefEq.respectTransparency false

/-- Fixed existence of the graded tensor coproducts on the actual slice.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
theorem sliceGradedTensor (P Q : GradedObject ℤ (SliceInternal Λ X U)) :
    P.HasTensor Q := inferInstance

attribute [local instance] sliceGradedTensor

/-- Fixed fourfold summand extensionality for the graded slice tensor.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
theorem sliceGradedTensorFour (P Q R S : GradedObject ℤ (SliceInternal Λ X U)) :
    GradedObject.HasTensor₄ObjExt P Q R S := inferInstance

/-- Fixed left iterated graded-tensor comparison on the slice.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
theorem sliceGradedTensorLeft (P Q R : GradedObject ℤ (SliceInternal Λ X U)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q R := inferInstance

/-- Fixed right iterated graded-tensor comparison on the slice.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
theorem sliceGradedTensorRight (P Q R : GradedObject ℤ (SliceInternal Λ X U)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q R := inferInstance

attribute [local instance] sliceGradedTensor sliceGradedTensorFour
  sliceGradedTensorLeft sliceGradedTensorRight

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native total tensor instance once for local cochains.
Source: Stacks 06YL; native Mod.monoidalCategoryCochainComplex
(auxiliary; not a blueprint node). -/
@[instance_reducible, instance] def sliceCochainMonoidal :
    MonoidalCategory (CochainComplex (SliceInternal Λ X U) ℤ) :=
  CategoryTheory.Mod.monoidalCategoryCochainComplex

/-- The native K-flat derived relative tensor for the actual restricted monoid.
Source: Stacks 06YS (auxiliary; not a blueprint node). -/
def sliceNativeTensor :
    DerivedCategory (SliceInternal Λ X U) × DerivedCategory (SliceInternal Λ X U) ⥤
      DerivedCategory (SliceInternal Λ X U) :=
  MonoidalCategory.tensor (DerivedCategory (SliceInternal Λ X U))

/-- The native total tensor on local internal complexes.
Source: Stacks 06YL (auxiliary; not a blueprint node). -/
def sliceTotalTensor (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    CochainComplex (SliceInternal Λ X U) ℤ :=
  (sliceCochainMonoidal Λ X U).tensorObj P Q

set_option backward.isDefEq.respectTransparency false in
/-- Fix the dependency's coproduct instance rather than rediscovering it by search.
Source: Stacks 012Z (auxiliary; not a blueprint node). -/
instance sliceTotalExists (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    P.HasMapBifunctor Q (curriedTensor (SliceInternal Λ X U)) :=
  comparison_internalTotalExists ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U) P Q

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] sliceComplexForward

set_option backward.isDefEq.respectTransparency false in
/-- The actual lax localization map for the native local tensor.
Source: Stacks 06YS (auxiliary; not a blueprint node). -/
def sliceLocalizationTensorMap (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceNativeTensor Λ X U).obj
      ((DerivedCategory.Q (C := SliceInternal Λ X U)).obj P,
        (DerivedCategory.Q (C := SliceInternal Λ X U)).obj Q) ⟶
      (DerivedCategory.Q (C := SliceInternal Λ X U)).obj (sliceTotalTensor Λ X U P Q) :=
  Functor.LaxMonoidal.μ (DerivedCategory.Q (C := SliceInternal Λ X U)) P Q

set_option backward.isDefEq.respectTransparency true

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
