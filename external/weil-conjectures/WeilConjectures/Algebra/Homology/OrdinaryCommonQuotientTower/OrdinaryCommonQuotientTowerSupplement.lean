/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CommonQuotientTowerPresentation.CommonQuotientTowerPresentationSupplement
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.OrdinaryFlatCoefficientComparison
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryCommonQuotientTower

/-! # Ordinary common-quotient scalar extensions

Source: Stacks Project, Modules on Sites, Tag 03EK (section-tensor-product).
The result concerns module sheaves before passing to complexes or derived categories.
Quotient units are proved epic, their local ideal-product kernels are computed, and their
transition compatibility follows from the pure-section formulas. The existence theorem
constructs the normalized ordinary comparison and coefficient transitions.
The quotient units themselves are constructed by the sheafification adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
universe u v r wR wB wS
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Mod" A:arg => ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J A)
set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Res" f:arg => restrictScalars
  ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

section QuotientKernel
variable {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)

private def K (U : Cᵒᵖ) : Ideal (R.obj.obj U) := RingHom.ker (q.hom.app U).hom

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem K_map {U V : Cᵒᵖ} (f : U ⟶ V) (a : R.obj.obj U)
    (ha : a ∈ K q U) : R.obj.map f a ∈ K q V := by
  change (q.hom.app V).hom (R.obj.map f a) = 0
  have h := CategoryTheory.congr_fun (q.hom.naturality f) a
  change (q.hom.app V).hom (R.obj.map f a) = S.obj.map f ((q.hom.app U).hom a) at h
  rw [h]
  change (q.hom.app U).hom a = 0 at ha
  rw [ha, map_zero]

private def quotientMap {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U) ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj V) (R.obj.obj V ⧸ K q V)) := by
  let g : R.obj.obj U →ₛₗ[(R.obj.map f).hom] R.obj.obj V :=
    { toFun := R.obj.map f
      map_add' := map_add (R.obj.map f).hom
      map_smul' := fun a b ↦ map_mul (R.obj.map f).hom a b }
  let h := (K q U).mapQ (K q V) g (fun a ha ↦ K_map q f a ha)
  exact ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U))
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj V) (R.obj.obj V ⧸ K q V)))
    { toFun := h
      map_add' := h.map_add
      map_smul' := fun a b ↦ h.map_smulₛₗ a b }

private def quotientPresheaf :
    PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R).obj where
  obj U := ModuleCat.of (R.obj.obj U) (R.obj.obj U ⧸ K q U)
  map f := quotientMap q f
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (R.obj.map (𝟙 U) x) = Submodule.Quotient.mk x
      exact congrArg Submodule.Quotient.mk
        (CategoryTheory.congr_fun (R.obj.map_id U) x)
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (R.obj.map (f ≫ g) x) =
        Submodule.Quotient.mk (R.obj.map g (R.obj.map f x))
      rw [Functor.map_comp]
      rfl

private def quotientToScalar : quotientPresheaf q ⟶
    ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
      (unit (derivedChangeRingIndependentCoefficients J S))).val where
  app U := ModuleCat.ofHom
    (X := (quotientPresheaf q).obj U)
    (Y := (((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
        (unit (derivedChangeRingIndependentCoefficients J S))).val.obj U))
    { toFun := RingHom.kerLift (q.hom.app U).hom
      map_add' := (RingHom.kerLift (q.hom.app U).hom).map_add
      map_smul' := by
        intro a x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change (q.hom.app U).hom (a * x) =
            (q.hom.app U).hom a * (q.hom.app U).hom x
          exact map_mul _ _ _ }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change (q.hom.app V).hom (R.obj.map f x) = S.obj.map f ((q.hom.app U).hom x)
      exact CategoryTheory.congr_fun (q.hom.naturality f) x

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem quotientToScalar_locallyInjective :
    PresheafOfModules.IsLocallyInjective J (quotientToScalar q) :=
  Presheaf.isLocallyInjective_of_injective J _ (fun U ↦ RingHom.kerLift_injective (q.hom.app U).hom)

omit [EssentiallySmall.{r} C] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] in
private theorem quotientToScalar_locallySurjective
    (hq : Presheaf.IsLocallySurjective J q.hom) :
    PresheafOfModules.IsLocallySurjective J (quotientToScalar q) := by
  constructor
  intro U s
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q.hom s)
  rintro V f ⟨r, hr⟩
  exact ⟨Submodule.Quotient.mk r, hr⟩

omit [EssentiallySmall.{r} C] in
private theorem tensor_quotientToScalar_locallyInjective
    (hq : Presheaf.IsLocallySurjective J q.hom)
    (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) :
    PresheafOfModules.IsLocallyInjective J (siteTensorHom (quotientToScalar q) M.val) := by
  have hI : PresheafOfModules.IsLocallyInjective J (quotientToScalar q) :=
    quotientToScalar_locallyInjective q
  have hS : PresheafOfModules.IsLocallySurjective J (quotientToScalar q) :=
    quotientToScalar_locallySurjective q hq
  let A := derivedChangeRingIndependentCoefficients J R
  let f := siteTensorHom (quotientToScalar q) M.val
  have : IsIso ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).map f) :=
    @PresheafOfModules.sheafification_tensorHom_isIso C _ J R.obj
      (quotientPresheaf q) _ M.val (quotientToScalar q) hI hS A.property _ _
  have : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf A.obj).map f)) :=
    inferInstanceAs (IsIso ((toSheaf A).map
      ((PresheafOfModules.sheafification (R := A) (𝟙 A.obj)).map f)))
  exact ((J.W_iff _).mpr this).isLocallyInjective

private theorem kernel_forward
    (hq : Presheaf.IsLocallySurjective J q.hom)
    (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (x : M.val.obj U)
    (hx : (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x) = 0) :
    Sieve.generate (fun (V : C) (f : V ⟶ U.unop) ↦
      M.val.map f.op x ∈ Submodule.span (R.obj.obj (op V))
        {y | ∃ j ∈ K q (op V), ∃ p : M.val.obj (op V), y = j • p}) ∈ J U.unop := by
  let A := derivedChangeRingIndependentCoefficients J R
  let Q := quotientPresheaf q
  let B := ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)).obj
    (unit (derivedChangeRingIndependentCoefficients J S))).val
  let f := siteTensorHom (quotientToScalar q) M.val
  let e : siteTensorPresheaf B M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).obj
          (changeOfRingsPresheaf q M) :=
    (siteTensorRightIso R M.val).app B ≪≫ (presheafTensorIso q M).symm
  let ψ := (PresheafOfModules.toPresheaf A.obj).map f ≫
    (PresheafOfModules.toPresheaf A.obj).map e.hom ≫
      toSheafify J (changeOfRingsPresheaf q M).presheaf
  have hLI : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf A.obj).map f) :=
    tensor_quotientToScalar_locallyInjective q hq M
  have : Presheaf.IsLocallyInjective J ψ := by
    dsimp only [ψ]
    have hE : Presheaf.IsLocallyInjective J
        ((PresheafOfModules.toPresheaf A.obj).map e.hom) := inferInstance
    have hθ : Presheaf.IsLocallyInjective J
        (toSheafify J (changeOfRingsPresheaf q M).presheaf) :=
      (J.W_toSheafify (changeOfRingsPresheaf q M).presheaf).isLocallyInjective
    exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ J _ _ _ _ _ hLI
      (@Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ J _ _ _ _ _ hE hθ)
  let z : (siteTensorPresheaf Q M.val).obj U :=
    (1 : R.obj.obj U ⧸ K q U) ⊗ₜ[R.obj.obj U] x
  have hzero : ψ.app U z = ψ.app U 0 := by
    rw [map_zero]
    change (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
      ((RingHom.kerLift (q.hom.app U).hom 1)
        ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) = 0
    rw [map_one]
    exact hx
  apply J.superset_covering ?_ (Presheaf.equalizerSieve_mem J ψ z 0 hzero)
  intro V g hg
  apply Sieve.le_generate
  change (siteTensorPresheaf Q M.val).map g.op z =
    (siteTensorPresheaf Q M.val).map g.op 0 at hg
  rw [map_zero] at hg
  change (quotientMap q g.op (1 : R.obj.obj U ⧸ K q U)) ⊗ₜ[R.obj.obj (op V)]
    M.val.restrictₛₗ g.op x = 0 at hg
  have h1 : quotientMap q g.op (1 : R.obj.obj U ⧸ K q U) =
      (1 : R.obj.obj (op V) ⧸ K q (op V)) := by
    change Submodule.Quotient.mk (R.obj.map g.op 1) = Submodule.Quotient.mk 1
    rw [map_one]
  rw [h1] at hg
  have hquot := congrArg
    (TensorProduct.quotTensorEquivQuotSMul (M.val.obj (op V)) (K q (op V))) hg
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at hquot
  have hmem : M.val.restrictₛₗ g.op x ∈ K q (op V) • (⊤ : Submodule _ (M.val.obj (op V))) :=
    (Submodule.Quotient.mk_eq_zero _).mp hquot
  have hle : K q (op V) • (⊤ : Submodule _ (M.val.obj (op V))) ≤
      Submodule.span (R.obj.obj (op V))
        {y | ∃ j ∈ K q (op V), ∃ p : M.val.obj (op V), y = j • p} := by
    rw [← Submodule.span_univ, ← (K q (op V)).span_eq, Submodule.span_smul_span]
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, p, _, rfl⟩
    exact Submodule.subset_span ⟨j, Ideal.subset_span hj, p, rfl⟩
  exact hle hmem

end QuotientKernel

omit [EssentiallySmall.{r} C] in
private theorem quotientPresheafUnit_locallySurjective
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (hq : Presheaf.IsLocallySurjective J q.hom) (M : Mod R) :
    PresheafOfModules.IsLocallySurjective J (commonQuotientPresheafUnit q M) := by
  let η := commonQuotientPresheafUnit q M
  constructor
  intro U t
  induction t using TensorProduct.inductionOn with
  | tmul r m =>
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q.hom r)
    rintro V f ⟨r', hr'⟩
    refine ⟨r' • (show M.val.obj (op V) from M.val.map f.op m), ?_⟩
    change (η.app _).hom (r' • (show M.val.obj (op V) from M.val.map f.op m)) =
      changeOfRingsMap q M f.op (r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] m)
    rw [(η.app _).hom.map_smul]
    rw [show changeOfRingsMap q M f.op
        (r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] m) =
        S.obj.map f.op r ⊗ₜ[R.obj.obj _, (q.hom.app _).hom] M.val.restrictₛₗ f.op m from
      Classical.choose_spec (exists_changeOfRingsMap q M f.op) r m]
    change (q.hom.app (op V) r') •
      ((1 : S.obj.obj (op V)) ⊗ₜ[R.obj.obj (op V), (q.hom.app (op V)).hom]
        (show M.val.obj (op V) from M.val.map f.op m)) = _
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    exact congrArg (fun s ↦ s ⊗ₜ[R.obj.obj (op V), (q.hom.app (op V)).hom]
      (show M.val.obj (op V) from M.val.map f.op m)) hr'
  | add x y hx hy =>
    apply J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V f ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m + n, ?_⟩
    change (η.app _).hom (m + n) = (changeOfRingsPresheaf q M).map f.op (x + y)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) hm hn

omit [EssentiallySmall.{r} C] in
private theorem quotientUnit_epi
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (hq : Presheaf.IsLocallySurjective J q.hom) (M : Mod R)
    (u : M ⟶ (Res q).obj (changeOfRings q M))
    (hu : ∀ (U : Cᵒᵖ) (x : M.val.obj U), u.val.app U x =
      (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x)) : Epi u := by
  have := quotientPresheafUnit_locallySurjective q hq M
  have hfac : (PresheafOfModules.toPresheaf _).map u.val =
      (PresheafOfModules.toPresheaf _).map (commonQuotientPresheafUnit q M) ≫
        toSheafify J (changeOfRingsPresheaf q M).presheaf := by
    ext U x
    exact hu U x
  have hlocal : PresheafOfModules.IsLocallySurjective J u.val := by
    change Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map u.val)
    rw [hfac]
    have : Presheaf.IsLocallySurjective J
        (toSheafify J (changeOfRingsPresheaf q M).presheaf) :=
      (J.W_toSheafify (changeOfRingsPresheaf q M).presheaf).isLocallySurjective
    exact Presheaf.isLocallySurjective_comp J _ _
  have : Sheaf.IsLocallySurjective ((toSheaf _).map u) := hlocal
  have : Epi ((toSheaf _).map u) := Sheaf.epi_of_isLocallySurjective _
  exact (toSheaf _).epi_of_epi_map inferInstance

omit [EssentiallySmall.{r} C] in
/-- The actual quotient unit has the prescribed section formula.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
theorem commonQuotientUnit_sections
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (commonQuotientUnit q M).val.app U x =
      (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x) := by
  rfl

section RingPushout

set_option backward.isDefEq.respectTransparency.types false

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ring_hasSheafify : HasSheafify J CommRingCat.{r} :=
  hasSheafifyEssentiallySmallSite J CommRingCat.{r}

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ring_locallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r} (CategoryTheory.forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{r} C).inverse.op)
        CommRingCat.{r} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{r} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem pushout_local
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (b : B ⟶ S)
    (h : IsPushout φ q b (𝟙 S)) :
    Presheaf.IsLocallyInjective J
      (pushout.desc b.hom (𝟙 S.obj) (by
        have hw := congrArg (fun f : R ⟶ S ↦ f.hom) h.w
        simpa using hw)) := by
  let := ring_hasSheafify (J := J)
  let := ring_locallyBijective (J := J)
  let P := pushout φ.hom q.hom
  let μ : P ⟶ S.obj := pushout.desc b.hom (𝟙 S.obj) (by
    have hw := congrArg (fun f : R ⟶ S ↦ f.hom) h.w
    simpa using hw)
  let adj := sheafificationAdjunction J CommRingCat.{r}
  let T := (presheafToSheaf J CommRingCat.{r}).obj P
  let iB : B ⟶ T := ⟨pushout.inl φ.hom q.hom ≫ toSheafify J P⟩
  let iS : S ⟶ T := ⟨pushout.inr φ.hom q.hom ≫ toSheafify J P⟩
  have hw : φ ≫ iB = q ≫ iS := by
    apply Sheaf.hom_ext
    change φ.hom ≫ pushout.inl φ.hom q.hom ≫ toSheafify J P =
      q.hom ≫ pushout.inr φ.hom q.hom ≫ toSheafify J P
    rw [← Category.assoc, pushout.condition, Category.assoc]
  let e := h.desc iB iS hw
  have he : e = iS := by
    have hh : 𝟙 S ≫ e = iS := h.inr_desc iB iS hw
    exact (Category.id_comp e).symm.trans hh
  have hb : b ≫ iS = iB := by rw [← he]; exact h.inl_desc iB iS hw
  let δ : T ⟶ S := (adj.homEquiv P S).symm μ
  have hδ : toSheafify J P ≫ δ.hom = μ :=
    (adj.homEquiv P S).apply_symm_apply μ
  have hleft : iS ≫ δ = 𝟙 S := by
    apply Sheaf.hom_ext
    change (pushout.inr φ.hom q.hom ≫ toSheafify J P) ≫ δ.hom = _
    rw [Category.assoc, hδ]
    exact pushout.inr_desc _ _ _
  have hright : δ ≫ iS = 𝟙 T := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ T.property
    change toSheafify J P ≫ (δ.hom ≫ iS.hom) = toSheafify J P ≫ 𝟙 _
    rw [← Category.assoc, hδ, Category.comp_id]
    apply pushout.hom_ext
    · change (pushout.inl φ.hom q.hom ≫
        pushout.desc b.hom (𝟙 S.obj) _) ≫ iS.hom = _
      rw [pushout.inl_desc]
      exact congrArg (fun f : B ⟶ T ↦ f.hom) hb
    · change (pushout.inr φ.hom q.hom ≫
        pushout.desc b.hom (𝟙 S.obj) _) ≫ iS.hom = _
      rw [pushout.inr_desc, Category.id_comp]
  have : IsIso δ := ⟨⟨iS, hright, hleft⟩⟩
  have : Presheaf.IsLocallyInjective J δ.hom := inferInstance
  have : Presheaf.IsLocallyInjective J (toSheafify J P) :=
    (J.W_toSheafify P).isLocallyInjective
  change Presheaf.IsLocallyInjective J μ
  rw [← hδ]
  infer_instance

private noncomputable def ringTensorIso
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    CommRingCat.of (B.obj.obj U ⊗[R.obj.obj U] S.obj.obj U) ≅
      (pushout φ.hom q.hom).obj U := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let h := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  exact (CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)).isoPushout ≪≫ h.isoPushout.symm

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_left
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      (x ⊗ₜ[R.obj.obj U] (1 : S.obj.obj U)) =
        (pushout.inl φ.hom q.hom).app U x := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)
  let he := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  have hh := congrArg (fun f : B.obj.obj U ⟶ (pushout φ.hom q.hom).obj U ↦ f x)
    ((ht.inl_isoPushout_hom_assoc he.isoPushout.inv).trans he.inl_isoPushout_inv)
  exact hh

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_right
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (y : S.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U] y) =
        (pushout.inr φ.hom q.hom).app U y := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)
  let he := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  exact congrArg (fun f : S.obj.obj U ⟶ (pushout φ.hom q.hom).obj U ↦ f y)
    ((ht.inr_isoPushout_hom_assoc he.isoPushout.inv).trans he.inr_isoPushout_inv)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_tmul
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) (y : S.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      (x ⊗ₜ[R.obj.obj U] y) =
        (pushout.inl φ.hom q.hom).app U x *
          (pushout.inr φ.hom q.hom).app U y := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  have ht : x ⊗ₜ[R.obj.obj U] y =
      (x ⊗ₜ[R.obj.obj U] (1 : S.obj.obj U)) *
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U] y) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul, ringTensorIso_left, ringTensorIso_right]

private noncomputable def multiplicationRaw
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
        ((Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))).val :=
  CoefficientOrdinaryProof.restrictionToTensor φ _ _ (𝟙 _)

private noncomputable def tensorRingEmbedding
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    (changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S))))).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat ⟶
      pushout φ.hom (φ ≫ b).hom ⋙ CategoryTheory.forget CommRingCat where
  app U := TypeCat.ofHom fun z ↦ (ringTensorIso φ (φ ≫ b) U).hom z
  naturality {U V} f := by
    ext z
    change (ringTensorIso φ (φ ≫ b) V).hom
      ((changeOfRingsPresheaf φ _).map f z) =
        (pushout φ.hom (φ ≫ b).hom).map f ((ringTensorIso φ (φ ≫ b) U).hom z)
    let := (φ.hom.app U).hom.toAlgebra
    let := ((φ ≫ b).hom.app U).hom.toAlgebra
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      change (ringTensorIso φ (φ ≫ b) V).hom
        ((changeOfRingsPresheaf φ _).map f (x + y)) =
          (pushout φ.hom (φ ≫ b).hom).map f
            ((ringTensorIso φ (φ ≫ b) U).hom (x + y))
      simp only [map_add, hx, hy]
    | tmul x y =>
      change (ringTensorIso φ (φ ≫ b) V).hom
        (changeOfRingsMap φ _ f (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] y)) = _
      rw [show changeOfRingsMap φ _ f
          (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] y) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ _ f) x y]
      rw [ringTensorIso_tmul]
      change _ = (pushout φ.hom (φ ≫ b).hom).map f
        ((ringTensorIso φ (φ ≫ b) U).hom (x ⊗ₜ[R.obj.obj U] y))
      rw [ringTensorIso_tmul, map_mul]
      exact congrArg₂ (· * ·)
        (NatTrans.naturality_apply (pushout.inl φ.hom (φ ≫ b).hom) f x)
        (NatTrans.naturality_apply (pushout.inr φ.hom (φ ≫ b).hom) f y)

private theorem multiplicationRaw_locallyInjective
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S)
    (h : IsPushout φ (φ ≫ b) b (𝟙 S)) :
    PresheafOfModules.IsLocallyInjective J (multiplicationRaw φ b) := by
  let μ : pushout φ.hom (φ ≫ b).hom ⟶ S.obj :=
    pushout.desc b.hom (𝟙 S.obj) (by rfl)
  have : Presheaf.IsLocallyInjective J μ := pushout_local φ (φ ≫ b) b h
  let e := tensorRingEmbedding φ b
  have : Presheaf.IsLocallyInjective J e :=
    Presheaf.isLocallyInjective_of_injective J e (fun U ↦
      (ConcreteCategory.bijective_of_isIso (ringTensorIso φ (φ ≫ b) U).hom).injective)
  have hfac : e ≫ Functor.whiskerRight μ (CategoryTheory.forget CommRingCat) =
      Functor.whiskerRight
        ((PresheafOfModules.toPresheaf _).map (multiplicationRaw φ b))
          (CategoryTheory.forget AddCommGrpCat) := by
    ext U z
    change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom z) =
      (multiplicationRaw φ b).app U z
    let := (φ.hom.app U).hom.toAlgebra
    let := ((φ ≫ b).hom.app U).hom.toAlgebra
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom (x + y)) =
        (multiplicationRaw φ b).app U (x + y)
      simp only [map_add, hx, hy]
    | tmul x y =>
      change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom (x ⊗ₜ[R.obj.obj U] y)) = _
      rw [ringTensorIso_tmul, map_mul]
      have hl := NatTrans.congr_app (pushout.inl_desc (f := φ.hom) (g := (φ ≫ b).hom)
        b.hom (𝟙 S.obj) (by rfl)) U
      have hr := NatTrans.congr_app (pushout.inr_desc (f := φ.hom) (g := (φ ≫ b).hom)
        b.hom (𝟙 S.obj) (by rfl)) U
      change μ.app U ((pushout.inl φ.hom (φ ≫ b).hom).app U x) *
        μ.app U ((pushout.inr φ.hom (φ ≫ b).hom).app U y) = _
      exact congrArg₂ (· * ·) (ConcreteCategory.congr_hom hl x)
        (ConcreteCategory.congr_hom hr y)
  apply (Presheaf.isLocallyInjective_forget_iff J _).mp
  rw [← hfac]
  infer_instance

private noncomputable def multiplicationSheaf
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    changeOfRings φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
        (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm (multiplicationRaw φ b)

omit [EssentiallySmall.{r} C] in
private theorem multiplicationSheaf_sections
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) (y : S.obj.obj U) :
    (multiplicationSheaf φ b).val.app U
      ((toSheafify J (changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
        (unit (derivedChangeRingIndependentCoefficients J S))))).presheaf).app U
          (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
            (show ((Res φ).obj ((Res b).obj
              (unit (derivedChangeRingIndependentCoefficients J S)))).val.obj U from y))) =
      b.hom.app U x * y := by
  let H := (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))
  let P := changeOfRingsPresheaf φ ((Res φ).obj H)
  have h := congrArg (fun f : P ⟶
      (PresheafOfModules.restrictScalars (𝟙 _)).obj H.val ↦ f.app U
        (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
          (show ((Res φ).obj H).val.obj U from y)))
      ((PresheafOfModules.sheafificationHomEquiv
        (R := derivedChangeRingIndependentCoefficients J B) (P := P) (F := H)
          (𝟙 _)).apply_symm_apply (multiplicationRaw φ b))
  exact h

private theorem multiplicationSheaf_isIso
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S)
    (h : IsPushout φ (φ ≫ b) b (𝟙 S)) : IsIso (multiplicationSheaf φ b) := by
  have := multiplicationRaw_locallyInjective φ b h
  have : PresheafOfModules.IsLocallySurjective J (multiplicationRaw φ b) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U y
    refine ⟨(1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
      (show ((Res φ).obj ((Res b).obj
        (unit (derivedChangeRingIndependentCoefficients J S)))).val.obj U from y), ?_⟩
    change b.hom.app U 1 * (show S.obj.obj U from y) = (show S.obj.obj U from y)
    rw [map_one, one_mul]
  have : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf _).map (multiplicationRaw φ b))) :=
    (J.W_iff _).mp (J.W_of_isLocallyBijective _)
  have : IsIso ((toSheaf _).map (multiplicationSheaf φ b)) := by
    unfold multiplicationSheaf
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    infer_instance
  exact isIso_of_reflects_iso _ (toSheaf _)

private noncomputable def ordinaryModelIso
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (F G : Mod R ⥤ Mod S)
    (hF : ∀ M, F.obj M = changeOfRings q M)
    (hG : ∀ M, G.obj M = changeOfRings q M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f =
      eqToHom (hF M) ≫ changeOfRingsHom q M f ≫ eqToHom (hF N).symm)
    (hmG : ∀ {M N} (f : M ⟶ N), G.map f =
      eqToHom (hG M) ≫ changeOfRingsHom q M f ≫ eqToHom (hG N).symm) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ eqToIso ((hF M).trans (hG M).symm)) (by
    intro M N f
    dsimp only [eqToIso.hom]
    rw [hmF, hmG]
    simp)

private theorem ordinaryComparison
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (b : B ⟶ S)
    (hpush : IsPushout φ q b (𝟙 S))
    [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wB} (Mod B)]
    [HasDerivedCategory.{wS} (Mod S)]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} q)
    (G : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} b) :
    ∃ e : Res φ ⋙ F.E ≅ G.E,
      ∀ (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U
          ((eqToHom (F.obj_eq ((Res φ).obj M)).symm).val.app U
            ((toSheafify J (changeOfRingsPresheaf q ((Res φ).obj M)).presheaf).app U
              (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x))) =
        (eqToHom (G.obj_eq M).symm).val.app U
          ((toSheafify J (changeOfRingsPresheaf b M).presheaf).app U
            (s ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] x)) := by
  have hq : φ ≫ b = q := by simpa using hpush.w
  subst q
  let EF := F.E
  let EG := G.E
  have hF := F.obj_eq
  have hG := G.obj_eq
  have hmF : ∀ {M M'} (f : M ⟶ M'), EF.map f =
      eqToHom (hF M) ≫ changeOfRingsHom (φ ≫ b) M f ≫ eqToHom (hF M').symm :=
    fun f ↦ F.map_eq f
  have hmG : ∀ {M M'} (f : M ⟶ M'), EG.map f =
      eqToHom (hG M) ≫ changeOfRingsHom b M f ≫ eqToHom (hG M').symm :=
    fun f ↦ G.map_eq f
  let : ∀ T : Sheaf J CommRingCat.{r}, HasDerivedCategory.{max (max u v) (r + 1)} (Mod T) :=
    fun T ↦ HasDerivedCategory.standard _
  obtain ⟨p, ⟨N⟩⟩ := SuccessiveDerivedQuotient.successive_derived_quotient_normalization
    (C := C) (J := J)
  let H := (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))
  have hm : (N.ordinaryAdjunction φ).counit.app H =
      eqToHom ((p φ).obj_eq ((Res φ).obj H)) ≫ multiplicationSheaf φ b := by
    apply ((N.ordinaryAdjunction φ).homEquiv _ _).injective
    have hh := (N.ordinaryAdjunction φ).homEquiv_symm_id H
    have hh' := ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H).apply_symm_apply
      (𝟙 ((Res φ).obj H))
    rw [hh] at hh'
    change ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H)
      ((N.ordinaryAdjunction φ).counit.app H) =
        ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H)
          (eqToHom ((p φ).obj_eq ((Res φ).obj H)) ≫ multiplicationSheaf φ b)
    rw [hh', Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = (multiplicationSheaf φ b).val.app U
      ((eqToHom ((p φ).obj_eq ((Res φ).obj H))).val.app U
        (((N.ordinaryAdjunction φ).unit.app ((Res φ).obj H)).val.app U x))
    rw [N.ordinary_unit]
    dsimp only [SuccessiveDerivedQuotient.sectionTensor, SuccessiveDerivedQuotient.pure]
    let z := (toSheafify J (changeOfRingsPresheaf φ ((Res φ).obj H)).presheaf).app U
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
    have hc : (eqToHom ((p φ).obj_eq ((Res φ).obj H))).val.app U
        ((eqToHom ((p φ).obj_eq ((Res φ).obj H)).symm).val.app U z) = z :=
      congrArg (fun k ↦ k.val.app U z)
        (eqToHom_trans ((p φ).obj_eq ((Res φ).obj H)).symm
          ((p φ).obj_eq ((Res φ).obj H)))
    rw [hc]
    change (show S.obj.obj U from x) = (multiplicationSheaf φ b).val.app U z
    rw [multiplicationSheaf_sections, map_one, one_mul]
  have hmul := multiplicationSheaf_isIso φ b hpush
  have hμ : IsIso ((N.ordinaryAdjunction φ).counit.app H) := by
    rw [hm]
    infer_instance
  obtain ⟨e, he⟩ := ordinary_flatCoefficientComparison p N φ b hμ
  let iF := ordinaryModelIso (φ ≫ b) EF (p (φ ≫ b)).ordinary hF
    (p (φ ≫ b)).obj_eq hmF (p (φ ≫ b)).map_eq
  let iG := ordinaryModelIso b EG (p b).ordinary hG (p b).obj_eq
    hmG (p b).map_eq
  refine ⟨Functor.isoWhiskerLeft (Res φ) iF ≪≫ e ≪≫ iG.symm, ?_⟩
  intro M U s x
  let P := (Res φ).obj M
  let z := (toSheafify J (changeOfRingsPresheaf (φ ≫ b) P).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, ((φ ≫ b).hom.app U).hom] x)
  let z' := (toSheafify J (changeOfRingsPresheaf b M).presheaf).app U
    (s ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] x)
  have hcF : eqToHom (hF P).symm ≫ iF.hom.app P =
      eqToHom ((p (φ ≫ b)).obj_eq P).symm := by
    change eqToHom (hF P).symm ≫
      eqToHom ((hF P).trans ((p (φ ≫ b)).obj_eq P).symm) = _
    simp
  have hcG : eqToHom ((p b).obj_eq M).symm ≫ iG.inv.app M =
      eqToHom (hG M).symm := by
    change eqToHom ((p b).obj_eq M).symm ≫
      eqToHom (((hG M).trans ((p b).obj_eq M).symm).symm) = _
    simp
  have hFi := congrArg (fun k ↦ k.val.app U z) hcF
  have hGi := congrArg (fun k ↦ k.val.app U z') hcG
  change (iF.hom.app P).val.app U ((eqToHom (hF P).symm).val.app U z) =
    (eqToHom ((p (φ ≫ b)).obj_eq P).symm).val.app U z at hFi
  have hp := he M U s x
  change (e.hom.app M).val.app U
    ((eqToHom ((p (φ ≫ b)).obj_eq P).symm).val.app U z) =
      (eqToHom ((p b).obj_eq M).symm).val.app U z' at hp
  change (iG.inv.app M).val.app U ((e.hom.app M).val.app U
    ((iF.hom.app P).val.app U ((eqToHom (hF P).symm).val.app U z))) = _
  rw [hFi, hp]
  exact hGi

omit [EssentiallySmall.{r} C] in
private theorem tensorSection_smul
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) =
      s • (show (changeOfRings q M).val.obj U from
        (commonQuotientUnit q M).val.app U x) := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := derivedChangeRingIndependentCoefficients J S) (𝟙 _)).unit.app
      (changeOfRingsPresheaf q M)
  change η.app U (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) =
    s • (η.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x))
  rw [← (η.app U).hom.map_smul]
  congr 1
  rw [ModuleCat.ExtendScalars.smul_tmul (f := (q.hom.app U).hom), mul_one]

private noncomputable def rawTransition
    {R S T : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (t : S ⟶ T) :
    CoefficientOrdinaryProof.tensorFunctor q ⋙ Res q ⟶
      CoefficientOrdinaryProof.tensorFunctor (q ≫ t) ⋙ Res (q ≫ t) := by
  let L := CoefficientOrdinaryProof.tensorFunctor q
  let L' := CoefficientOrdinaryProof.tensorFunctor (q ≫ t)
  let i := SuccessiveDerivedQuotient.resComp q t
  let v : 𝟭 (Mod R) ⟶ L' ⋙ Res t ⋙ Res q :=
    { app := fun M ↦ commonQuotientUnit (q ≫ t) M ≫ i.inv.app (L'.obj M)
      naturality := by
        intro M N f
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact congrArg (fun k ↦ k.val.app U x)
          (commonQuotientUnit_naturality (q ≫ t) f) }
  let f : L ⟶ L' ⋙ Res t :=
    { app := fun M ↦ (CoefficientOrdinaryProof.tensorHomEquiv q M _).symm (v.app M)
      naturality := by
        intro M N g
        apply (CoefficientOrdinaryProof.tensorHomEquiv q M _).injective
        rw [CoefficientOrdinaryProof.tensorHomEquiv_naturality_left,
          CoefficientOrdinaryProof.tensorHomEquiv_naturality_right,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact v.naturality g }
  exact Functor.whiskerRight f (Res q) ≫ (Functor.isoWhiskerLeft L' i).hom

private theorem rawTransition_unit
    {R S T : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (t : S ⟶ T)
    (M : Mod R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((rawTransition q t).app M).val.app U ((commonQuotientUnit q M).val.app U x) =
      (commonQuotientUnit (q ≫ t) M).val.app U x := by
  let H := (Res t).obj (changeOfRings (q ≫ t) M)
  let v : M ⟶ (Res q).obj H := commonQuotientUnit (q ≫ t) M ≫
    (SuccessiveDerivedQuotient.resComp q t).inv.app (changeOfRings (q ≫ t) M)
  have h := congrArg (fun f : M ⟶ (Res q).obj H ↦ f.val.app U x)
    ((CoefficientOrdinaryProof.tensorHomEquiv q M H).apply_symm_apply v)
  exact h

private theorem rawTransition_sections
    {R S T : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (t : S ⟶ T)
    (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((rawTransition q t).app M).val.app U
      ((toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x)) =
      (toSheafify J (changeOfRingsPresheaf (q ≫ t) M).presheaf).app U
        (t.hom.app U s ⊗ₜ[R.obj.obj U, ((q ≫ t).hom.app U).hom] x) := by
  let H := (Res t).obj (changeOfRings (q ≫ t) M)
  let v : M ⟶ (Res q).obj H := commonQuotientUnit (q ≫ t) M ≫
    (SuccessiveDerivedQuotient.resComp q t).inv.app (changeOfRings (q ≫ t) M)
  let f := (CoefficientOrdinaryProof.tensorHomEquiv q M H).symm v
  have hf : f.val.app U
      ((commonQuotientUnit q M).val.app U x) =
        (commonQuotientUnit (q ≫ t) M).val.app U x := rawTransition_unit q t M U x
  change f.val.app U _ = _
  rw [tensorSection_smul, (f.val.app U).hom.map_smul]
  change t.hom.app U s • (show (changeOfRings (q ≫ t) M).val.obj U from
    f.val.app U ((commonQuotientUnit q M).val.app U x)) = _
  rw [hf, tensorSection_smul]

attribute [local irreducible] rawTransition

private theorem modelTransition
    {R S T : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (q' : R ⟶ T) (t : S ⟶ T)
    (h : q ≫ t = q')
    [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wS} (Mod S)]
    [HasDerivedCategory.{wB} (Mod T)]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} q)
    (G : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wB} q') :
    ∃ δ : F.E ⋙ Res q ⟶ G.E ⋙ Res q',
      ∀ (M : Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (δ.app M).val.app U
          ((eqToHom (F.obj_eq M).symm).val.app U
            ((toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
              (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x))) =
        (eqToHom (G.obj_eq M).symm).val.app U
          ((toSheafify J (changeOfRingsPresheaf q' M).presheaf).app U
            (t.hom.app U s ⊗ₜ[R.obj.obj U, (q'.hom.app U).hom] x)) := by
  subst q'
  let iF := ordinaryModelIso q F.E (CoefficientOrdinaryProof.tensorFunctor q)
    F.obj_eq (fun _ ↦ rfl) (fun f ↦ F.map_eq f) (fun f ↦ by simp; rfl)
  let iG := ordinaryModelIso (q ≫ t) G.E
    (CoefficientOrdinaryProof.tensorFunctor (q ≫ t))
    G.obj_eq (fun _ ↦ rfl) (fun f ↦ G.map_eq f) (fun f ↦ by simp; rfl)
  refine ⟨(Functor.isoWhiskerRight iF (Res q)).hom ≫ rawTransition q t ≫
    (Functor.isoWhiskerRight iG (Res (q ≫ t))).inv, ?_⟩
  intro M U s x
  let z := (toSheafify J (changeOfRingsPresheaf q M).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x)
  have hc : eqToHom (F.obj_eq M).symm ≫ iF.hom.app M = 𝟙 _ := by
    change eqToHom (F.obj_eq M).symm ≫ eqToHom (F.obj_eq M) = _
    simp
  have hcz := congrArg (fun k ↦ k.val.app U z) hc
  change (iF.hom.app M).val.app U ((eqToHom (F.obj_eq M).symm).val.app U z) = z
    at hcz
  change (iG.inv.app M).val.app U ((rawTransition q t).app M |>.val.app U
    ((iF.hom.app M).val.app U ((eqToHom (F.obj_eq M).symm).val.app U z))) = _
  rw [hcz, rawTransition_sections]
  rfl

end RingPushout

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wB} (Mod B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Mod(D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ,
    DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

variable {D a b}

/-- The constructed quotient units have the normalized pure-section formula.
Source: Stacks 03EK (blueprint: lem-weil-pbc-ordinary-common-quotient-tower). -/
theorem OrdinaryCommonQuotientTower.unit_sections
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) (M : Mod R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((O.unit n).app M).val.app U x =
      (eqToHom ((a n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
          ((1 : (D.S.obj (op n)).obj.obj U)
            ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x)) := by
  rfl

/-- The pure-section transition formula forces compatibility of quotient units.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: evaluate the transition on 1 tensor x. Ring transitions preserve 1,
so the result is exactly the unit at the next level. Equality on sections proves
componentwise equality and therefore equality of natural transformations. -/
theorem OrdinaryCommonQuotientTower.unit_transition
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) :
    O.unit (n + 1) ≫ O.transition n = O.unit n := by
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  change ((O.transition n).app M).val.app U
    (((O.unit (n + 1)).app M).val.app U x) = ((O.unit n).app M).val.app U x
  rw [O.unit_sections, O.transition_sections, O.unit_sections, map_one]

/-- The normalized quotient unit is epi using local scalar lifts and tensor generation.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: the presheaf unit is locally surjective by induction on tensors: lift a pure
scalar along the local quotient projection; sums lift on the intersection cover.
Sheafification units are locally surjective, so the composite is locally surjective
and therefore epi. Transport along the prescribed ordinary object equality. -/
theorem OrdinaryCommonQuotientTower.unit_epi
    (O : OrdinaryCommonQuotientTower D a b) (n : ℕ) (M : Mod R) :
    Epi ((O.unit n).app M) := by
  let e := (Res (D.projection n)).mapIso (eqToIso ((a n).obj_eq M))
  let u := (O.unit n).app M ≫ e.hom
  have : Epi u := quotientUnit_epi (D.projection n) (D.q_surjective n) M u (by
    intro U x
    have h := O.unit_sections n M U x
    change (e.hom.val.app U) (((O.unit n).app M).val.app U x) = _
    rw [h]
    change (eqToHom ((a n).obj_eq M)).val.app U
      ((eqToHom ((a n).obj_eq M).symm).val.app U _) = _
    exact congrArg (fun f ↦ f.val.app U
      ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
        ((1 : (D.S.obj (op n)).obj.obj U)
          ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x)))
      (eqToHom_trans ((a n).obj_eq M).symm ((a n).obj_eq M)))
  have h : Epi (u ≫ e.inv) := inferInstance
  simpa [u, Category.assoc] using h

/-- The section normalizations determine all ordinary comparison data uniquely.
Source: Stacks 03EK
(blueprint: lem-weil-pbc-ordinary-common-quotient-tower).
Proof: units agree on every section. For a transition or a comparison, restrict
scalars to R and precompose with the epic quotient unit. The formulas at 1 tensor x
make the resulting maps equal on every section. Cancel the unit; restriction leaves
the underlying functions unchanged, so the original maps agree. Proof fields are
irrelevant. This also verifies that choosing the normalized data is unambiguous. -/
theorem OrdinaryCommonQuotientTower.unique
    (O O' : OrdinaryCommonQuotientTower D a b) : O = O' := by
  have ht : O.transition = O'.transition := by
    funext n
    apply NatTrans.ext
    funext M
    have := O.unit_epi (n + 1) M
    apply (cancel_epi ((O.unit (n + 1)).app M)).mp
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((O.transition n).app M).val.app U
      (((O.unit (n + 1)).app M).val.app U x) =
        ((O'.transition n).app M).val.app U (((O.unit (n + 1)).app M).val.app U x)
    simp only [O.unit_sections]
    exact (O.transition_sections n M U 1 x).trans (O'.transition_sections n M U 1 x).symm
  have ho : O.ordinary = O'.ordinary := by
    funext n
    apply Iso.ext
    apply NatTrans.ext
    funext M
    let Q := Res (D.projection n)
    let P := (Res φ).obj M
    have := O.unit_epi n P
    have hQ : Q.map ((O.ordinary n).hom.app M) =
        Q.map ((O'.ordinary n).hom.app M) := by
      apply (cancel_epi ((O.unit n).app P)).mp
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((O.ordinary n).hom.app M).val.app U
        (((O.unit n).app P).val.app U x) =
          ((O'.ordinary n).hom.app M).val.app U (((O.unit n).app P).val.app U x)
      simp only [O.unit_sections]
      exact (O.ordinary_sections n M U 1 x).trans (O'.ordinary_sections n M U 1 x).symm
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f ↦ f.val.app U x) hQ
  cases O
  cases O'
  dsimp only at ht ho
  cases ht
  cases ho
  rfl

variable (D a b)

end SheafOfModules
