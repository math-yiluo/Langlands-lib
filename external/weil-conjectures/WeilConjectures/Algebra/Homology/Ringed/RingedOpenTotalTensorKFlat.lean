/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Total tensor and K-flatness for ringed slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor),
Homology, Tag 012Z, and Cohomology on Sites, Tags 06YN and 06YS
(blueprint: lem-sf-ringed-open-total-tensor-kflat).

The total tensor is Mathlib's direct-sum total cochain complex. Both module functors
are the existing localized-system functors, applied termwise. The site object and
morphism universes remain independent; coefficients live in a universe containing both.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules

variable {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max c v r}) (U : S)

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenExtension :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  localizedSystemExtension.{c, v, r} R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenRestriction :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  localizedSystemRestriction.{c, v, r} R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafTensorLeft :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  ringedSliceTensorLeft.{c, max c r, v} J R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafTensorRight :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  ringedSliceTensorRight.{c, max c r, v} J R U

/-- Termwise application of the actual direct-sum extension followed by sheafification.
Source: Stacks Project, Modules on Sites, Tags 03DI--03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
abbrev ringedOpenExtensionOnComplexes :
    CochainComplex (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).over U)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI := localizedSystemExtensionAdditive.{c, v, r} R U
  (localizedSystemExtension.{c, v, r} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise restriction to the localized ringed site.
Source: Stacks Project, Modules on Sites, Tags 04IX and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
abbrev ringedOpenRestrictionOnComplexes :
    CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).over U)) ℤ :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI := localizedSystemRestrictionAdditive.{c, v, r} R U
  (localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The existing sheaf tensor with its coefficient ring specified explicitly.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  @curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) _
    (cochainModulesMonoidal.{c, v, max c v r} A)

/-- Zero-map preservation for the specified existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :
    (ringedOpenTensor.{c, v, r} A).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs ((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).PreservesZeroMorphisms)

/-- Zero-map preservation in the second variable of the existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorObjZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    (M : SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :
    ((ringedOpenTensor.{c, v, r} A).obj M).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs (((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).obj M).PreservesZeroMorphisms)

/-- The existing total tensor has the required direct sums on this small ringed site.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenHasTotalTensor {T : Type c} [Category.{v} T]
    {K : GrothendieckTopology T} (A : Sheaf K CommRingCat.{max c v r})
    (P C : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ) :
    P.HasMapBifunctor C (ringedOpenTensor.{c, v, r} A) :=
  letI : HasSheafify K AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := K)
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := K)
  inferInstance

/-- The existing total tensor bifunctor, with its canonical instances supplied explicitly.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  letI := ringedOpenTensorZero.{c, v, r} A
  letI := ringedOpenTensorObjZero.{c, v, r} A
  letI := ringedOpenHasTotalTensor.{c, v, r} A
  (ringedOpenTensor.{c, v, r} A).map₂CochainComplex

/-- The canonical insertion of one bidegree into the existing direct-sum total tensor.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTensorι {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    (P C : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    ((ringedOpenTensor.{c, v, r} A).obj (P.X p)).obj (C.X q) ⟶
      (((ringedOpenTotalTensor.{c, v, r} A).obj P).obj C).X n :=
  letI := ringedOpenTensorZero.{c, v, r} A
  letI := ringedOpenTensorObjZero.{c, v, r} A
  letI := ringedOpenHasTotalTensor.{c, v, r} A
  CochainComplex.ιMapBifunctor P C (ringedOpenTensor.{c, v, r} A) p q n h

/-- The simultaneous map of the existing total tensor bifunctor on two chain maps.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensorMap {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    {P P' C C' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((ringedOpenTotalTensor.{c, v, r} A).obj P).obj C ⟶
      ((ringedOpenTotalTensor.{c, v, r} A).obj P').obj C' :=
  (((ringedOpenTotalTensor.{c, v, r} A).map a).app C) ≫
    ((ringedOpenTotalTensor.{c, v, r} A).obj P').map b

/-- The recorded sheaf comparison, expressed in the existing monoidal tensor.
Source: Stacks Project, Modules on Sites, Tag 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafComparison
    (θ : ringedOpenSheafTensorLeft.{c, v, r} R U ≅
      ringedOpenSheafTensorRight.{c, v, r} R U)
    (M : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    (ringedOpenExtension.{c, v, r} R U).obj
        (((ringedOpenTensor.{max c v, v, r} (R.over U)).obj M).obj
          ((ringedOpenRestriction.{c, v, r} R U).obj N)) ≅
      ((ringedOpenTensor.{c, v, r} R).obj
        ((ringedOpenExtension.{c, v, r} R U).obj M)).obj N :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI := cochainTensorLocalizationIsMonoidal.{c, v, max c v r} R
  letI := cochainTensorLocalizationIsMonoidal.{max c v, v, max c v r} (R.over U)
  (ringedOpenExtension.{c, v, r} R U).mapIso
      (tensorObjIsoSheafification.{v, max c v, max c v r} (R := R.over U) M
        ((ringedOpenRestriction.{c, v, r} R U).obj N)) ≪≫
    θ.app (M, N) ≪≫
    (tensorObjIsoSheafification.{v, c, max c v r} (R := R)
      ((ringedOpenExtension.{c, v, r} R U).obj M) N).symm

private theorem precompose_preservesZero
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (H : A ⥤ A ⥤ D) [H.PreservesZeroMorphisms]
    (T : B ⥤ A) :
    (H ⋙ (Functor.whiskeringLeft B A D).obj T).PreservesZeroMorphisms := by
  constructor
  intro M M'
  apply NatTrans.ext
  funext N
  change (H.map 0).app (T.obj N) = 0
  rw [Functor.map_zero]
  rfl

private theorem precompose_obj_preservesZero
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (H : A ⥤ A ⥤ D) [∀ M, (H.obj M).PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms] (M : A) :
    ((H ⋙ (Functor.whiskeringLeft B A D).obj T).obj M).PreservesZeroMorphisms :=
  inferInstanceAs (T ⋙ H.obj M).PreservesZeroMorphisms

private theorem precompose_hasTotal
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (H : A ⥤ A ⥤ D) [H.PreservesZeroMorphisms]
    [∀ M, (H.obj M).PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A D).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A D).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ) :
    HomologicalComplex.HasMapBifunctor P C
      (H ⋙ (Functor.whiskeringLeft B A D).obj T) (.up ℤ) :=
  inferInstanceAs (HomologicalComplex.HasMapBifunctor P
    ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ))

private theorem map₂_map_eq {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [Preadditive D₃]
    (F : D₁ ⥤ D₂ ⥤ D₃) [F.PreservesZeroMorphisms]
    [∀ M, (F.obj M).PreservesZeroMorphisms]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₂ ℤ),
      HomologicalComplex.HasMapBifunctor P C F (.up ℤ)]
    {P P' : CochainComplex D₁ ℤ} {C C' : CochainComplex D₂ ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((F.map₂CochainComplex.map a).app C) ≫ (F.map₂CochainComplex.obj P').map b =
      HomologicalComplex.mapBifunctorMap a b F (.up ℤ) := by
  ext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp [HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]

private theorem mapBifunctorMap_precompose
    {D₁ D₂ D₃ D₄ : Type*} [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
    [HasZeroMorphisms D₁] [HasZeroMorphisms D₂] [HasZeroMorphisms D₃] [Preadditive D₄]
    (H : D₁ ⥤ D₃ ⥤ D₄) (T : D₂ ⥤ D₃) [T.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₃ ℤ),
      HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P : CochainComplex D₁ ℤ) (C : CochainComplex D₂ ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T) (.up ℤ)]
    {P P' : CochainComplex D₁ ℤ} {C C' : CochainComplex D₂ ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    HomologicalComplex.mapBifunctorMap a b
        (H ⋙ (Functor.whiskeringLeft D₂ D₃ D₄).obj T) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
        H (.up ℤ) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change _ = HomologicalComplex.ιMapBifunctor P
      ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ) p q n h ≫ _
  rw [HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.ι_mapBifunctorMap]
  rfl

private theorem comparison_precompose_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ⟶
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
          H (.up ℤ)) ≫ HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P' C' =
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P C ≫
        HomologicalComplex.mapBifunctorMap ((E.mapHomologicalComplex (.up ℤ)).map a)
          b H' (.up ℤ) := by
  rw [← mapBifunctorMap_precompose H T a b]
  exact HomologicalComplex.mapBifunctorComparison_naturality τ (.up ℤ) a b

@[irreducible] private def comparisonPrecomposeIso
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ) :
    (E.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P ((T.mapHomologicalComplex (.up ℤ)).obj C) H) ≅
      CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj P) C H' :=
  asIso (HomologicalComplex.mapBifunctorComparison τ.hom (.up ℤ) P C)

private theorem comparisonPrecomposeIso_ι
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    (P : CochainComplex A ℤ) (C : CochainComplex B ℤ)
    (p q n : ℤ) (h : p + q = n) :
    E.map (HomologicalComplex.ιMapBifunctor P
        ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ) p q n h) ≫
        (comparisonPrecomposeIso E T H H' τ P C).hom.f n =
      (τ.hom.app (P.X p)).app (C.X q) ≫
        HomologicalComplex.ιMapBifunctor
          ((E.mapHomologicalComplex (.up ℤ)).obj P) C H' (.up ℤ) p q n h := by
  unfold comparisonPrecomposeIso
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    τ.hom (.up ℤ) P C p q n h

private theorem comparisonPrecomposeIso_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a ((T.mapHomologicalComplex (.up ℤ)).map b)
          H (.up ℤ)) ≫ (comparisonPrecomposeIso E T H H' τ P' C').hom =
      (comparisonPrecomposeIso E T H H' τ P C).hom ≫
        HomologicalComplex.mapBifunctorMap ((E.mapHomologicalComplex (.up ℤ)).map a)
          b H' (.up ℤ) := by
  unfold comparisonPrecomposeIso
  exact comparison_precompose_natural E T H H' τ.hom a b

private theorem comparisonPrecomposeIso_map₂_natural
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    {P P' : CochainComplex A ℤ} {C C' : CochainComplex B ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    (E.mapHomologicalComplex (.up ℤ)).map
        (((H.map₂CochainComplex.map a).app ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≫
          (H.map₂CochainComplex.obj P').map ((T.mapHomologicalComplex (.up ℤ)).map b)) ≫
        (comparisonPrecomposeIso E T H H' τ P' C').hom =
      (comparisonPrecomposeIso E T H H' τ P C).hom ≫
        (((H'.map₂CochainComplex.map ((E.mapHomologicalComplex (.up ℤ)).map a)).app C) ≫
          (H'.map₂CochainComplex.obj
            ((E.mapHomologicalComplex (.up ℤ)).obj P')).map b) := by
  rw [map₂_map_eq, map₂_map_eq]
  exact comparisonPrecomposeIso_natural E T H H' τ a b

private abbrev TotalInclusions {A : Type*} [Category* A] [Preadditive A]
    (H : A ⥤ A ⥤ A)
    (total : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ) :=
  ∀ (P C : CochainComplex A ℤ) (p q n : ℤ) (_h : p + q = n),
    (H.obj (P.X p)).obj (C.X q) ⟶ ((total.obj P).obj C).X n

private structure TotalTensorPresentation {A : Type*} [Category* A] [Preadditive A]
    (H : A ⥤ A ⥤ A) [H.PreservesZeroMorphisms]
    [∀ M, (H.obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    (total : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (ι : TotalInclusions H total) : Prop where
  functor_eq : total = H.map₂CochainComplex
  inclusion_heq : ∀ P C p q n h,
    HEq (ι P C p q n h) (HomologicalComplex.ιMapBifunctor P C H (.up ℤ) p q n h)

private theorem ringedOpenTotalTensor_presentation
    {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :
    let := ringedOpenTensorZero.{c, v, r} A
    let := ringedOpenTensorObjZero.{c, v, r} A
    let := ringedOpenHasTotalTensor.{c, v, r} A
    TotalTensorPresentation (ringedOpenTensor.{c, v, r} A)
      (ringedOpenTotalTensor.{c, v, r} A) (ringedOpenTensorι.{c, v, r} A) := by
  let := ringedOpenTensorZero.{c, v, r} A
  let := ringedOpenTensorObjZero.{c, v, r} A
  let := ringedOpenHasTotalTensor.{c, v, r} A
  refine ⟨rfl, ?_⟩
  intro P C p q n h
  rfl

private theorem comparisonPrecompose_exists
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H') :
    ∃ Φ : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      (E.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P ((T.mapHomologicalComplex (.up ℤ)).obj C) H) ≅
        CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj P) C H',
      (∀ P C (p q n : ℤ) (h : p + q = n),
        E.map (HomologicalComplex.ιMapBifunctor P
            ((T.mapHomologicalComplex (.up ℤ)).obj C) H (.up ℤ) p q n h) ≫
            (Φ P C).hom.f n =
          (τ.hom.app (P.X p)).app (C.X q) ≫
            HomologicalComplex.ιMapBifunctor
              ((E.mapHomologicalComplex (.up ℤ)).obj P) C H' (.up ℤ) p q n h) ∧
      (∀ (P P' : CochainComplex A ℤ) (C C' : CochainComplex B ℤ)
          (a : P ⟶ P') (b : C ⟶ C'),
        (E.mapHomologicalComplex (.up ℤ)).map
            (((H.map₂CochainComplex.map a).app
                ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≫
              (H.map₂CochainComplex.obj P').map ((T.mapHomologicalComplex (.up ℤ)).map b)) ≫
            (Φ P' C').hom =
          (Φ P C).hom ≫
            (((H'.map₂CochainComplex.map
                ((E.mapHomologicalComplex (.up ℤ)).map a)).app C) ≫
              (H'.map₂CochainComplex.obj
                ((E.mapHomologicalComplex (.up ℤ)).obj P')).map b)) := by
  refine ⟨comparisonPrecomposeIso E T H H' τ, ?_, ?_⟩
  · intro P C p q n h
    exact comparisonPrecomposeIso_ι E T H H' τ P C p q n h
  · intro P P' C C' a b
    exact comparisonPrecomposeIso_map₂_natural E T H H' τ a b

private theorem comparisonPresented_exists
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (τ : (Functor.postcompose₂.obj E).obj
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H')
    (FA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (FB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (ιA : TotalInclusions H FA) (ιB : TotalInclusions H' FB)
    (hFA : TotalTensorPresentation H FA ιA)
    (hFB : TotalTensorPresentation H' FB ιB) :
    ∃ Φ : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      (E.mapHomologicalComplex (.up ℤ)).obj
          ((FA.obj P).obj ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≅
        (FB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj C,
      (∀ P C (p q n : ℤ) (h : p + q = n),
        E.map (ιA P ((T.mapHomologicalComplex (.up ℤ)).obj C) p q n h) ≫
            (Φ P C).hom.f n =
          (τ.hom.app (P.X p)).app (C.X q) ≫
            ιB ((E.mapHomologicalComplex (.up ℤ)).obj P) C p q n h) ∧
      (∀ (P P' : CochainComplex A ℤ) (C C' : CochainComplex B ℤ)
          (a : P ⟶ P') (b : C ⟶ C'),
        (E.mapHomologicalComplex (.up ℤ)).map
            (((FA.map a).app ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≫
              (FA.obj P').map ((T.mapHomologicalComplex (.up ℤ)).map b)) ≫
            (Φ P' C').hom =
          (Φ P C).hom ≫
            (((FB.map ((E.mapHomologicalComplex (.up ℤ)).map a)).app C) ≫
              (FB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P')).map b)) := by
  rcases hFA with ⟨eFA, eιA⟩
  rcases hFB with ⟨eFB, eιB⟩
  subst FA
  subst FB
  have hιA : ιA = fun P C p q n h ↦
      HomologicalComplex.ιMapBifunctor P C H (.up ℤ) p q n h := by
    funext P C p q n h
    exact eq_of_heq (eιA P C p q n h)
  have hιB : ιB = fun P C p q n h ↦
      HomologicalComplex.ιMapBifunctor P C H' (.up ℤ) p q n h := by
    funext P C p q n h
    exact eq_of_heq (eιB P C p q n h)
  subst ιA
  subst ιB
  exact comparisonPrecompose_exists E T H H' τ

@[irreducible] private def bifunctorIsoOfComponents {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃] (F G : D₁ ⥤ D₂ ⥤ D₃)
    (e : ∀ M N, (F.obj M).obj N ≅ (G.obj M).obj N)
    (h : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      (F.map a).app N ≫ (F.obj M').map b ≫ (e M' N').hom =
        (e M N).hom ≫ (G.map a).app N ≫ (G.obj M').map b) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (e M) (by
    intro N N' b
    simpa using h (𝟙 M) b)) (by
      intro M M' a
      apply NatTrans.ext
      funext N
      simpa using h a (𝟙 N))

private theorem bifunctorIsoOfComponents_hom {D₁ D₂ D₃ : Type*}
    [Category* D₁] [Category* D₂] [Category* D₃] (F G : D₁ ⥤ D₂ ⥤ D₃)
    (e : ∀ M N, (F.obj M).obj N ≅ (G.obj M).obj N)
    (h : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      (F.map a).app N ≫ (F.obj M').map b ≫ (e M' N').hom =
        (e M N).hom ≫ (G.map a).app N ≫ (G.obj M').map b)
    (M : D₁) (N : D₂) :
    (((bifunctorIsoOfComponents F G e h).hom.app M).app N) = (e M N).hom := by
  unfold bifunctorIsoOfComponents
  rfl

private theorem comparisonFromComponents_exists
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (E : A ⥤ B) [E.Additive] [PreservesColimitsOfSize.{0, 0} E]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (H : A ⥤ A ⥤ A) (H' : B ⥤ B ⥤ B)
    [H.PreservesZeroMorphisms] [∀ M, (H.obj M).PreservesZeroMorphisms]
    [H'.PreservesZeroMorphisms] [∀ M, (H'.obj M).PreservesZeroMorphisms]
    [(H ⋙ (Functor.whiskeringLeft B A A).obj T).PreservesZeroMorphisms]
    [∀ M, ((H ⋙ (Functor.whiskeringLeft B A A).obj T).obj M).PreservesZeroMorphisms]
    [∀ (P C : CochainComplex A ℤ), HomologicalComplex.HasMapBifunctor P C H (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ), HomologicalComplex.HasMapBifunctor P C H' (.up ℤ)]
    [∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C
        (H ⋙ (Functor.whiskeringLeft B A A).obj T) (.up ℤ)]
    (e : ∀ (M : A) (N : B),
      E.obj ((H.obj M).obj (T.obj N)) ≅ (H'.obj (E.obj M)).obj N)
    (h : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      E.map ((H.map a).app (T.obj N) ≫ (H.obj M').map (T.map b)) ≫
          (e M' N').hom =
        (e M N).hom ≫ (H'.map (E.map a)).app N ≫ (H'.obj (E.obj M')).map b)
    (FA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (FB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (ιA : TotalInclusions H FA) (ιB : TotalInclusions H' FB)
    (hFA : TotalTensorPresentation H FA ιA)
    (hFB : TotalTensorPresentation H' FB ιB) :
    ∃ Φ : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      (E.mapHomologicalComplex (.up ℤ)).obj
          ((FA.obj P).obj ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≅
        (FB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj C,
      (∀ P C (p q n : ℤ) (h : p + q = n),
        E.map (ιA P ((T.mapHomologicalComplex (.up ℤ)).obj C) p q n h) ≫
            (Φ P C).hom.f n =
          (e (P.X p) (C.X q)).hom ≫
            ιB ((E.mapHomologicalComplex (.up ℤ)).obj P) C p q n h) ∧
      (∀ (P P' : CochainComplex A ℤ) (C C' : CochainComplex B ℤ)
          (a : P ⟶ P') (b : C ⟶ C'),
        (E.mapHomologicalComplex (.up ℤ)).map
            (((FA.map a).app ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≫
              (FA.obj P').map ((T.mapHomologicalComplex (.up ℤ)).map b)) ≫
            (Φ P' C').hom =
          (Φ P C).hom ≫
            (((FB.map ((E.mapHomologicalComplex (.up ℤ)).map a)).app C) ≫
              (FB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P')).map b)) := by
  let F := H ⋙ (Functor.whiskeringLeft B A A).obj T
  let τ : (Functor.postcompose₂.obj E).obj F ≅
      (((Functor.whiskeringLeft₂ B).obj E).obj (𝟭 B)).obj H' :=
    bifunctorIsoOfComponents _ _ e (by
      intro M M' N N' a b
      change E.map ((H.map a).app (T.obj N)) ≫
          E.map ((H.obj M').map (T.map b)) ≫ (e M' N').hom =
        (e M N).hom ≫ (H'.map (E.map a)).app N ≫ (H'.obj (E.obj M')).map b
      rw [← Category.assoc, ← E.map_comp]
      exact h a b)
  obtain ⟨Φ, hι, hn⟩ := comparisonPresented_exists E T H H' τ FA FB ιA ιB hFA hFB
  refine ⟨Φ, ?_, hn⟩
  intro P C p q n h
  simpa only [τ, bifunctorIsoOfComponents_hom] using hι P C p q n h

private theorem acyclic_map {D D' : Type*} [Category* D] [Category* D']
    [Abelian D] [Abelian D'] (G : D ⥤ D') [G.Additive] [G.PreservesHomology]
    (K : CochainComplex D ℤ) (hK : K.Acyclic) :
    ((G.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro n
  exact (show (K.sc n).Exact from hK n).map G

private theorem tensor_acyclic_swap {D : Type*} [Category* D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (P C : CochainComplex D ℤ)
    [HomologicalComplex.HasMapBifunctor P C (curriedTensor D) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor C P (curriedTensor D) (.up ℤ)]
    [SymmetricCategory D]
    (h : (CochainComplex.mapBifunctor P C (curriedTensor D)).Acyclic) :
    (CochainComplex.mapBifunctor C P (curriedTensor D)).Acyclic := by
  let F := curriedTensor D
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj C) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj C) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ (P.X p) (C.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right (P.X p) (C.d q q')).symm))
      (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left (P.d p p') (C.X q)).symm)
  intro n
  exact (h n).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso C P F (.up ℤ))

private theorem kFlat_map_of_comparison
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [SymmetricCategory A] [SymmetricCategory B]
    [∀ (P C : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor A) (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor B) (.up ℤ)]
    (E : A ⥤ B) [E.PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (hE : ∀ K : CochainComplex A ℤ, K.Acyclic →
      ((E.mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hT : ∀ K : CochainComplex B ℤ, K.Acyclic →
      ((T.mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (e : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      (E.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P ((T.mapHomologicalComplex (.up ℤ)).obj C)
            (curriedTensor A)) ≅
        CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj P) C
          (curriedTensor B))
    (P : CochainComplex A ℤ)
    (hP : ∀ C : CochainComplex A ℤ, C.Acyclic →
      (CochainComplex.mapBifunctor C P (curriedTensor A)).Acyclic) :
    ∀ C : CochainComplex B ℤ, C.Acyclic →
      (CochainComplex.mapBifunctor C ((E.mapHomologicalComplex (.up ℤ)).obj P)
        (curriedTensor B)).Acyclic := by
  intro C hC
  have hc := hT C hC
  have hp := hP ((T.mapHomologicalComplex (.up ℤ)).obj C) hc
  have hp' := tensor_acyclic_swap (D := A) _ _ hp
  have he := hE _ hp'
  apply tensor_acyclic_swap (D := B)
  intro n
  exact (he n).of_iso (e P C)

private theorem kFlat_map_of_presented_comparison
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [SymmetricCategory A] [SymmetricCategory B]
    [∀ (P C : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor A) (.up ℤ)]
    [∀ (P C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor B) (.up ℤ)]
    (E : A ⥤ B) [E.PreservesZeroMorphisms]
    (T : B ⥤ A) [T.PreservesZeroMorphisms]
    (hE : ∀ K : CochainComplex A ℤ, K.Acyclic →
      ((E.mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (hT : ∀ K : CochainComplex B ℤ, K.Acyclic →
      ((T.mapHomologicalComplex (.up ℤ)).obj K).Acyclic)
    (FA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (FB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (eFA : FA = (curriedTensor A).map₂CochainComplex)
    (eFB : FB = (curriedTensor B).map₂CochainComplex)
    (e : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      (E.mapHomologicalComplex (.up ℤ)).obj
          ((FA.obj P).obj ((T.mapHomologicalComplex (.up ℤ)).obj C)) ≅
        (FB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).obj C)
    (P : CochainComplex A ℤ)
    (hP : ∀ C : CochainComplex A ℤ, C.Acyclic →
      ((FA.obj C).obj P).Acyclic) :
    ∀ C : CochainComplex B ℤ, C.Acyclic →
      ((FB.obj C).obj ((E.mapHomologicalComplex (.up ℤ)).obj P)).Acyclic := by
  subst FA
  subst FB
  exact kFlat_map_of_comparison E T hE hT e P hP

private theorem compose_three_squares {D : Type*} [Category* D]
    {A B C D₀ A' B' C' D' : D}
    {a : A ⟶ B} {b : B ⟶ C} {d : C ⟶ D₀}
    {a' : A' ⟶ B'} {b' : B' ⟶ C'} {d' : C' ⟶ D'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'} {i : D₀ ⟶ D'}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) (hd : h ≫ d' = d ≫ i) :
    f ≫ (a' ≫ b' ≫ d') = (a ≫ b ≫ d) ≫ i := by
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, hd]

private theorem inverse_square {D : Type*} [Category* D]
    {A B A' B' : D} (e : A ≅ B) (e' : A' ≅ B') (f : A ⟶ A') (g : B ⟶ B')
    (h : f ≫ e'.hom = e.hom ≫ g) : g ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

private theorem tensorNatural_from_squares {D D' : Type*} [Category* D] [Category* D']
    [MonoidalCategory D] [MonoidalCategory D'] (L : D' ⥤ D) [L.Monoidal]
    {M M' N N' : D} {X X' Y Y' : D'} (a : M ⟶ M') (b : N ⟶ N')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (u : M ⟶ L.obj X) (u' : M' ⟶ L.obj X')
    (w : N ⟶ L.obj Y) (w' : N' ⟶ L.obj Y')
    (ha : a ≫ u' = u ≫ L.map f) (hb : b ≫ w' = w ≫ L.map g) :
    (a ⊗ₘ b) ≫ ((u' ⊗ₘ w') ≫ Functor.LaxMonoidal.μ L X' Y') =
      ((u ⊗ₘ w) ≫ Functor.LaxMonoidal.μ L X Y) ≫ L.map (f ⊗ₘ g) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, ha, hb, ← tensorHom_comp_tensorHom,
    Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc]

-- Keep the inverse counit as a natural transformation throughout the tensor calculation.
private theorem tensorSheafification_natural
    {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify K AddCommGrpCat.{r}]
    (A : Sheaf K CommRingCat.{r})
    [(K.W.inverseImage (PresheafOfModules.toPresheaf.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)).IsMonoidal]
    {M M' N N' : SheafOfModules.{r}
      ((sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A)}
    (a : M ⟶ M') (b : N ⟶ N') :
    let := monoidalCategory.{v, c, r} A
    (a ⊗ₘ b) ≫ (tensorObjIsoSheafification.{v, c, r} (R := A) M' N').hom =
      (tensorObjIsoSheafification.{v, c, r} (R := A) M N).hom ≫
        (PresheafOfModules.sheafification.{r} (𝟙 _)).map (a.val ⊗ₘ b.val) := by
  let := monoidalCategory.{v, c, r} A
  let L := PresheafOfModules.sheafification.{r}
    (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A) (𝟙 _)
  let e := asIso (PresheafOfModules.sheafificationAdjunction.{r}
    (R := (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A) (𝟙 _)).counit
  have ha := e.inv.naturality a
  have hb := e.inv.naturality b
  change a ≫ e.inv.app M' = e.inv.app M ≫ L.map a.val at ha
  change b ≫ e.inv.app N' = e.inv.app N ≫ L.map b.val at hb
  change (a ⊗ₘ b) ≫ ((e.inv.app M' ⊗ₘ e.inv.app N') ≫
      Functor.LaxMonoidal.μ L M'.val N'.val) =
    ((e.inv.app M ⊗ₘ e.inv.app N) ≫ Functor.LaxMonoidal.μ L M.val N.val) ≫
      L.map (a.val ⊗ₘ b.val)
  exact tensorNatural_from_squares L a b a.val b.val
    (e.inv.app M) (e.inv.app M') (e.inv.app N) (e.inv.app N') ha hb

private theorem sheafComparison_natural
    (θ : ringedOpenSheafTensorLeft.{c, v, r} R U ≅
      ringedOpenSheafTensorRight.{c, v, r} R U)
    {M M' : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)}
    {N N' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (a : M ⟶ M') (b : N ⟶ N') :
    (ringedOpenExtension.{c, v, r} R U).map
        (((ringedOpenTensor.{max c v, v, r} (R.over U)).map a).app
          ((ringedOpenRestriction.{c, v, r} R U).obj N) ≫
        ((ringedOpenTensor.{max c v, v, r} (R.over U)).obj M').map
          ((ringedOpenRestriction.{c, v, r} R U).map b)) ≫
        (ringedOpenSheafComparison.{c, v, r} R U θ M' N').hom =
      (ringedOpenSheafComparison.{c, v, r} R U θ M N).hom ≫
        (((ringedOpenTensor.{c, v, r} R).map ((ringedOpenExtension.{c, v, r} R U).map a)).app N ≫
          ((ringedOpenTensor.{c, v, r} R).obj
            ((ringedOpenExtension.{c, v, r} R U).obj M')).map b) := by
  let : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  let := cochainModulesMonoidal.{c, v, max c v r} R
  let : MonoidalCategory (SheafOfModules.{max c v r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) :=
    cochainModulesMonoidal.{max c v, v, max c v r} (R.over U)
  let := cochainTensorLocalizationIsMonoidal.{c, v, max c v r} R
  let := cochainTensorLocalizationIsMonoidal.{max c v, v, max c v r} (R.over U)
  have h₁ := tensorSheafification_natural.{max c v, v, max c v r} (R.over U) a
    ((ringedOpenRestriction.{c, v, r} R U).map b)
  have h₂ := tensorSheafification_natural.{c, v, max c v r} R
    ((ringedOpenExtension.{c, v, r} R U).map a) b
  have hθ := θ.hom.naturality (show (M, N) ⟶ (M', N') from (a, b))
  change _ ≫ ((ringedOpenExtension.{c, v, r} R U).map
      (tensorObjIsoSheafification.{v, max c v, max c v r} (R := R.over U) M'
        ((ringedOpenRestriction.{c, v, r} R U).obj N')).hom ≫ θ.hom.app (M', N') ≫
      (tensorObjIsoSheafification.{v, c, max c v r} (R := R)
        ((ringedOpenExtension.{c, v, r} R U).obj M') N').inv) =
    ((ringedOpenExtension.{c, v, r} R U).map
      (tensorObjIsoSheafification.{v, max c v, max c v r} (R := R.over U) M
        ((ringedOpenRestriction.{c, v, r} R U).obj N)).hom ≫ θ.hom.app (M, N) ≫
      (tensorObjIsoSheafification.{v, c, max c v r} (R := R)
        ((ringedOpenExtension.{c, v, r} R U).obj M) N).inv) ≫ _
  exact compose_three_squares
    (by
      simp only [ringedOpenTensor, curriedTensor_map_app, curriedTensor_obj_map,
        ← tensorHom_def]
      simpa only [ringedOpenSheafTensorLeft, ringedSliceTensorLeft,
        ringedOpenExtension, localizedSystemExtension, Functor.comp_map, Functor.prod_map,
        MonoidalCategory.tensor_map, ringedOpenRestriction, localizedSystemRestriction,
        forget_map, sheafCompose_obj_obj, Functor.map_comp] using
        congrArg (ringedOpenExtension.{c, v, r} R U).map h₁)
    hθ (inverse_square _ _ _ _ h₂)

/-- An explicit API for the tensor presentation used by the K-flat predicate. -/
private theorem kFlat_totalTensor_iff
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ↔
      ∀ C : CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ,
        C.Acyclic → (((ringedOpenTotalTensor.{c, v, r} R).obj C).obj P).Acyclic := by
  rfl

set_option maxHeartbeats 200000 in
-- The comparison simultaneously tracks the three independent universes.
/-- The sheaf tensor comparison extends to unbounded direct-sum total tensor complexes,
with its prescribed map on every summand and naturality in both chain maps. Extension
also preserves K-flat complexes and K-flat resolutions.

Source: Stacks Project, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor),
Homology, Tags 012Z and 010N, and Cohomology on Sites, Tags 06YN and 06YS
(blueprint: lem-sf-ringed-open-total-tensor-kflat).

Proof:
1. In each degree n use the extension/restriction adjunction
   (lem-pur-site-restriction-module-adjunction-exact) and preservation of colimits by
   a left adjoint (situation-conventions) to commute extension
   with the sum over p+q=n. Compose the inverse coproduct comparison with the sum of
   the sheaf tensor isomorphisms (lem-weil-pbc-ringed-slice-extension-tensor). This
   gives precisely the displayed equation on each insertion of a tensor summand.
2. Naturality of the sheaf comparison for (d_P,1) and (1,d_C) identifies the two
   differential components. Additivity of extension preserves the sign (-1)^p.
   Thus these degreewise isomorphisms commute with d_P tensor 1 + (-1)^p 1 tensor d_C
   (def-pc-tensor-complex-sheaves). The same equations for arbitrary chain maps give
   the displayed naturality. Each source summand has just these two differential
   components, so no infinite sum into a fixed summand occurs.
3. The tensor symmetry sends the (a,b) summand to (b,a), multiplying the ordinary
   sheaf tensor interchange (def-pur-sheaf-tensor-product) by (-1)^(ab). For dy tensor x
   the two differential coefficients are (-1)^(ab), and for y tensor dx they are
   (-1)^(ab+b)=(-1)^((a+1)b). The composite of two interchanges is the identity.
4. For acyclic C, exact restriction makes j^*C acyclic by the natural homology
   comparison (lem-sp-exact-functor-preserves-homology). K-flatness of P makes
   Tot(j^*C tensor P) acyclic (def-pc-kflat-complex). Apply the signed interchange,
   exact extension, the total comparison, and the signed interchange again. This
   proves Tot(C tensor j_!P) acyclic, the defining K-flatness test.
5. For a K-flat resolution f:P -> H, exact extension preserves the quasi-isomorphism:
   the homology comparison identifies H^n(j_!f) with j_!H^n(f), which is invertible.
   Step 4 supplies K-flatness of its source. All sums are direct sums indexed by
   integer pairs; neither boundedness nor constancy of R has been used. -/
theorem ringedOpen_totalTensor_kFlat :
    (∃ θ : ringedOpenSheafTensorLeft.{c, v, r} R U ≅
        ringedOpenSheafTensorRight.{c, v, r} R U,
      ∃ Φ : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
          (((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
          (C : CochainComplex (SheafOfModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ),
        (ringedOpenExtensionOnComplexes.{c, v, r} R U).obj
            (((ringedOpenTotalTensor.{max c v, v, r} (R.over U)).obj P).obj
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).obj C)) ≅
          ((ringedOpenTotalTensor.{c, v, r} R).obj
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)).obj C,
      (∀ P C (p q n : ℤ) (h : p + q = n),
        (ringedOpenExtension.{c, v, r} R U).map
            (ringedOpenTensorι.{max c v, v, r} (R.over U) P
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).obj C) p q n h) ≫
            (Φ P C).hom.f n =
          (ringedOpenSheafComparison.{c, v, r} R U θ (P.X p) (C.X q)).hom ≫
            ringedOpenTensorι.{c, v, r} R
              ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P) C p q n h) ∧
      (∀ P P' C C' (a : P ⟶ P') (b : C ⟶ C'),
        (ringedOpenExtensionOnComplexes.{c, v, r} R U).map
            (ringedOpenTotalTensorMap.{max c v, v, r} (R.over U) a
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).map b)) ≫ (Φ P' C').hom =
          (Φ P C).hom ≫ ringedOpenTotalTensorMap.{c, v, r} R
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map a) b)) ∧
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)) ∧
    (∀ (P H : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ) (f : P ⟶ H),
      CochainComplex.IsKFlatResolutionIndependentCoefficients (R := R.over U) f →
        CochainComplex.IsKFlatResolutionIndependentCoefficients (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map f)) := by
  let : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  let A := SheafOfModules.{max c v r}
    (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)
  let B := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let E : A ⥤ B := localizedSystemExtension.{c, v, r} R U
  let T : B ⥤ A := localizedSystemRestriction.{c, v, r} R U
  let : E.Additive := localizedSystemExtensionAdditive.{c, v, r} R U
  let : T.Additive := localizedSystemRestrictionAdditive.{c, v, r} R U
  let : PreservesFiniteLimits E := localizedSystemExtensionLimits.{c, v, r} R U
  let : PreservesFiniteColimits E := localizedSystemExtensionColimits.{c, v, r} R U
  let : PreservesFiniteLimits T := localizedSystemRestrictionLimits.{c, v, r} R U
  let : PreservesFiniteColimits T := localizedSystemRestrictionColimits.{c, v, r} R U
  let : PreservesColimitsOfSize.{0, 0} E :=
    (localizedSystemAdjunction.{c, v, r} R U).leftAdjoint_preservesColimits
  let : MonoidalCategory A :=
    cochainModulesMonoidal.{max c v, v, max c v r} (R.over U)
  let : MonoidalCategory B := cochainModulesMonoidal.{c, v, max c v r} R
  let : MonoidalPreadditive A :=
    cochainModulesPreadditive.{max c v, v, max c v r} (R.over U)
  let : MonoidalPreadditive B := cochainModulesPreadditive.{c, v, max c v r} R
  let : SymmetricCategory A :=
    cochainModulesSymmetric.{max c v, v, max c v r} (R.over U)
  let : SymmetricCategory B := cochainModulesSymmetric.{c, v, max c v r} R
  let H : A ⥤ A ⥤ A := ringedOpenTensor.{max c v, v, r} (R.over U)
  let : H.PreservesZeroMorphisms := ringedOpenTensorZero.{max c v, v, r} (R.over U)
  let : ∀ M, (H.obj M).PreservesZeroMorphisms :=
    ringedOpenTensorObjZero.{max c v, v, r} (R.over U)
  let F : A ⥤ B ⥤ A := H ⋙ (Functor.whiskeringLeft B A A).obj T
  let F' : B ⥤ B ⥤ B := ringedOpenTensor.{c, v, r} R
  let : F'.PreservesZeroMorphisms := ringedOpenTensorZero.{c, v, r} R
  let : ∀ M, (F'.obj M).PreservesZeroMorphisms := ringedOpenTensorObjZero.{c, v, r} R
  let : F.PreservesZeroMorphisms := precompose_preservesZero H T
  let : ∀ M, (F.obj M).PreservesZeroMorphisms := precompose_obj_preservesZero H T
  let : ∀ (P C : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P C H (.up ℤ) :=
    ringedOpenHasTotalTensor.{max c v, v, r} (R.over U)
  let : ∀ (P C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C F' (.up ℤ) :=
    ringedOpenHasTotalTensor.{c, v, r} R
  let : ∀ (P C : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor A) (.up ℤ) :=
    ringedOpenHasTotalTensor.{max c v, v, r} (R.over U)
  let : ∀ (P C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C (curriedTensor B) (.up ℤ) :=
    ringedOpenHasTotalTensor.{c, v, r} R
  let : ∀ (P : CochainComplex A ℤ) (C : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P C F (.up ℤ) := precompose_hasTotal H T
  have hex : Nonempty (ringedOpenSheafTensorLeft.{c, v, r} R U ≅
      ringedOpenSheafTensorRight.{c, v, r} R U) :=
    ringedSlice_extension_tensor.{c, max c r, v} J R U
  obtain ⟨θ'⟩ := hex
  -- Totalize the comparison and retain its equation on every tensor summand.
  obtain ⟨Φ, hΦι, hΦnat⟩ :=
    comparisonFromComponents_exists (A := A) (B := B) E T H F'
      (fun M N ↦ ringedOpenSheafComparison.{c, v, r} R U θ' M N)
      (fun a b ↦ sheafComparison_natural.{c, v, r} R U θ' a b)
      (ringedOpenTotalTensor.{max c v, v, r} (R.over U))
      (ringedOpenTotalTensor.{c, v, r} R)
      (ringedOpenTensorι.{max c v, v, r} (R.over U))
      (ringedOpenTensorι.{c, v, r} R)
      (ringedOpenTotalTensor_presentation.{max c v, v, r} (R.over U))
      (ringedOpenTotalTensor_presentation.{c, v, r} R)
  -- Exactness and the signed interchange transport the K-flat acyclicity test.
  have hk : ∀ P : CochainComplex A ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P) := by
    intro P hP
    apply (kFlat_totalTensor_iff.{c, v, r} R _).mpr
    exact kFlat_map_of_presented_comparison (A := A) (B := B) E T
      (acyclic_map E) (acyclic_map T)
      (ringedOpenTotalTensor.{max c v, v, r} (R.over U))
      (ringedOpenTotalTensor.{c, v, r} R)
      (ringedOpenTotalTensor_presentation.{max c v, v, r} (R.over U)).functor_eq
      (ringedOpenTotalTensor_presentation.{c, v, r} R).functor_eq Φ P
      ((kFlat_totalTensor_iff.{max c v, v, r} (R.over U) P).mp hP)
  refine ⟨⟨θ', Φ, ?_, ?_⟩, hk, ?_⟩
  · intro P C p q n h
    simpa only [ringedOpenExtension,
      ringedOpenExtensionOnComplexes, ringedOpenRestrictionOnComplexes] using
      hΦι P C p q n h
  · intro P P' C C' a b
    simpa only [ringedOpenTotalTensorMap] using
      hΦnat P P' C C' a b
  · intro P H f hf
    have := hf.1
    exact ⟨inferInstance, hk P hf.2⟩

end SheafOfModules
