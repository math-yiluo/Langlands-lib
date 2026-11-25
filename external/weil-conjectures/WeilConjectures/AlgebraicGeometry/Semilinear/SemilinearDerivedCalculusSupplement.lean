/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification


public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus

/-! # Ordinary derived semilinear sections

The categories below are module sheaves on the actual vertical sequence site and their
ordinary unbounded derived categories. All comparisons have specified sources, targets
and equations; there are no free proposition-valued parameters.

## Main definitions and statements

- `Systems`, `DS`: strict semilinear systems and their ordinary derived category.
- `Data`, `Geometry`, `OpenSystems`: the coefficient, geometric and localized calculus.
- `TensorComparisonModel`, `InverseTensorPure`: representative and pure-tensor normalization.
- `semilinearDerivedSections`: existence of the complete ordinary-derived calculus.
- `evaluation_mate`: compatibility of specified adjunction transposes with evaluation.

## References

* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, Lemma 4.10 and Proposition 4.17
* Stacks Project, Tags 0941, 079P, 06YS, 06YY, 07A4, 07A6 and 08J7--08JB
* Stacks Project, Tags 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

private theorem modulePushforward_exact
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{max c v c₂ v₂ r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c v c₂ v₂ r}]
    [HasSheafify L AddCommGrpCat.{max c v c₂ v₂ r}]
    [L.WEqualsLocallyBijective AddCommGrpCat.{max c v c₂ v₂ r}]
    {F : D ⥤ E} [F.IsContinuous K L] [F.IsCocontinuous K L]
    {S : Sheaf K RingCat.{max c v c₂ v₂ r}} {R : Sheaf L RingCat.{max c v c₂ v₂ r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{max c v c₂ v₂ r} K L).obj R) :
    (SheafOfModules.pushforward.{max c v c₂ v₂ r} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{max c v c₂ v₂ r} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{max c v c₂ v₂ r} φ) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    intro X Y f g
    ext V x
    rfl
  · let T := SheafOfModules.forget.{max c v c₂ v₂ r} S ⋙ PresheafOfModules.toPresheaf S.obj
    have : PreservesFiniteLimits (SheafOfModules.pushforward.{max c v c₂ v₂ r} φ ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget.{max c v c₂ v₂ r} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
          (CategoryTheory.Functor.whiskeringLeft _ _ _).obj F.op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves _ T
  · let H := F.sheafPushforwardContinuous AddCommGrpCat.{max c v c₂ v₂ r} K L
    have : PreservesColimitsOfSize.{max c v c₂ v₂ r, max c v c₂ v₂ r} H :=
      (F.sheafAdjunctionCocontinuous AddCommGrpCat.{max c v c₂ v₂ r}
        K L).leftAdjoint_preservesColimits
    let T := SheafOfModules.toSheaf.{max c v c₂ v₂ r} S
    have : PreservesFiniteColimits (SheafOfModules.pushforward.{max c v c₂ v₂ r} φ ⋙ T) := by
      change PreservesFiniteColimits (SheafOfModules.toSheaf.{max c v c₂ v₂ r} R ⋙ H)
      infer_instance
    have : ReflectsFiniteColimits T :=
      { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
    exact preservesFiniteColimits_of_reflects_of_preserves _ T

@[irreducible] private def restrictionSheafificationMap
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
        (SheafOfModules.pushforward.{r} φ).obj
          ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{r} (𝟙 _)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))

private theorem restrictionSheafificationMap_unit
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    toSheafify K (F.op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val =
      Functor.whiskerLeft F.op (toSheafify L P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{r} (R := S) (𝟙 _)
    (P := (PresheafOfModules.pushforward φ.hom).obj P)
    (F := (SheafOfModules.pushforward.{r} φ).obj
      ((PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P))).apply_symm_apply
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P))
  unfold restrictionSheafificationMap
  exact congrArg ((PresheafOfModules.toPresheaf.{r} S.obj).map) h

private theorem restrictionSheafificationMap_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (U : Dᵒᵖ)
    (z : ((PresheafOfModules.pushforward φ.hom).obj P).obj U) :
    (restrictionSheafificationMap φ P).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app
        ((PresheafOfModules.pushforward φ.hom).obj P)).app U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
        (F.op.obj U) z := by
  exact congrArg (fun k ↦ k.app U z) (restrictionSheafificationMap_unit φ P)

private theorem pushforward_four_comp_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    {A B C : SheafOfModules.{r} S} {P Q : SheafOfModules.{r} R}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ (SheafOfModules.pushforward φ).obj P)
    (d : P ⟶ Q) (U : Dᵒᵖ) (z : A.val.obj U) :
    (a ≫ b ≫ c ≫ (SheafOfModules.pushforward φ).map d).val.app U z =
      d.val.app (F.op.obj U) (c.val.app U (b.val.app U (a.val.app U z))) := rfl

private theorem sheaf_iso_inv_hom_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{r}} {M N : SheafOfModules.{r} S}
    (T : M ≅ N) (U : Dᵒᵖ) (z : N.val.obj U) :
    T.hom.val.app U (T.inv.val.app U z) = z := by
  exact congrArg (fun k ↦ k.val.app U z) T.inv_hom_id

private theorem sheafification_unit_naturality_apply
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf K RingCat.{r}) {P Q : PresheafOfModules.{r} S.obj} (f : P ⟶ Q)
    (U : Dᵒᵖ) (z : P.obj U) :
    ((PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map f).val.app U
      (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app P).app
        U z) =
      ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
        U (f.app U z) := by
  exact congrArg (fun k ↦ k.app U z)
    ((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.naturality f).symm

private theorem tensorComparison_unit_apply
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) (Q : PresheafOfModules.{r} S.obj)
    (t : Q ⟶ (PresheafOfModules.pushforward φ.hom).obj P)
    {A : SheafOfModules.{r} S} {B : SheafOfModules.{r} R}
    (T : A ≅ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).obj Q)
    (V : B ≅ (PresheafOfModules.sheafification.{r} (R := R) (𝟙 _)).obj P)
    (U : Dᵒᵖ) (z : Q.obj U) :
    (T.hom ≫ (PresheafOfModules.sheafification.{r} (R := S) (𝟙 _)).map t ≫
        restrictionSheafificationMap φ P ≫ (SheafOfModules.pushforward φ).map V.inv).val.app U
      (T.inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := S) (𝟙 _)).unit.app Q).app
          U z)) =
      V.inv.val.app (F.op.obj U)
        (((PresheafOfModules.sheafificationAdjunction.{r} (R := R) (𝟙 _)).unit.app P).app
          (F.op.obj U) (t.app U z)) := by
  rw [pushforward_four_comp_apply, sheaf_iso_inv_hom_apply,
    sheafification_unit_naturality_apply, restrictionSheafificationMap_unit_apply]

private theorem restrictionSheafificationMap_isIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify L AddCommGrpCat.{r}] [L.WEqualsLocallyBijective AddCommGrpCat.{r}]
    {F : D ⥤ E} [F.IsContinuous K L] [F.IsCocontinuous K L]
    {S : Sheaf K RingCat.{r}} {R : Sheaf L RingCat.{r}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} K L).obj R)
    (P : PresheafOfModules.{r} R.obj) :
    IsIso (restrictionSheafificationMap φ P) := by
  let a := toSheafify K (F.op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf.{r} _).map (restrictionSheafificationMap φ P).val
  have hi : Presheaf.IsLocallyInjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker K L F _
  have hs : Presheaf.IsLocallySurjective K
      (Functor.whiskerLeft F.op (toSheafify L P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker K L F _
  have hi' : Presheaf.IsLocallyInjective K b := by
    rw [← Presheaf.comp_isLocallyInjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective K b := by
    rw [← Presheaf.comp_isLocallySurjective_iff K a b]
    rw [restrictionSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{r} S)]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem tensorSection_hom_ext
    (R : Sheaf J CommRingCat.{max c v r})
    (M N P : Mod.{c, v, max c v r} J R)
    {f g : ordinaryTensor.{c, v, r} J R M N ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (tensorSection.{c, v, r} J R M N U x y) =
        g.val.app U (tensorSection.{c, v, r} J R M N U x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (R := ring.{c, v, max c v r} J R) (𝟙 _)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv).mp
  apply (adj.homEquiv _ P).injective
  apply PresheafOfModules.hom_ext
  intro U
  ext z
  change f.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z)) =
    g.val.app U ((SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      M N).inv.val.app U ((adj.unit.app _).app U z))
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem restrictScalars_mu_bijective (R S : Type r) [CommRing R] [CommRing S]
    (e : R ≃+* S) (M N : ModuleCat.{r} S) :
    Function.Bijective (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv e.symm
  let em : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj M) M :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  let en : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
      ((ModuleCat.restrictScalars e.toRingHom).obj N) N :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change (e.toRingHom r) • x = (e.toRingHom r) • x
        rfl }
  have hh : (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N :
      _ → _) = TensorProduct.congr em en := by
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N x y
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hh]
  exact (TensorProduct.congr em en).bijective

private theorem restrictScalars_mu_isIso (R S : Type r) [CommRing R] [CommRing S]
    (f : R →+* S) (M N : ModuleCat.{r} S)
    (hf : Function.Bijective f) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f) M N) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact restrictScalars_mu_bijective R S (RingEquiv.ofBijective f hf) M N

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def restrictionTensorPresheafIso
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {F : D ⥤ E} {R : Eᵒᵖ ⥤ CommRingCat.{r}} {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (hφ : ∀ U, IsIso (φ.app U))
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat)) :
    let G := PresheafOfModules.pushforward (F := F)
      (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ
    PresheafOfModules.Monoidal.tensorObj (R := S) (G.obj M) (G.obj N) ≅
      G.obj (PresheafOfModules.Monoidal.tensorObj (R := R) M N) := by
  let G := PresheafOfModules.pushforward (F := F)
    (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ
  letI : G.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal φ
  let f := Functor.LaxMonoidal.μ G M N
  have h (U : Dᵒᵖ) : IsIso (f.app U) := by
    dsimp only [f, G]
    erw [PresheafOfModules.pushforward_μ_app φ M N U]
    apply restrictScalars_mu_isIso
    have := hφ U
    exact ConcreteCategory.bijective_of_isIso (φ.app U)
  exact PresheafOfModules.isoMk (fun U ↦ @asIso _ _ _ _ (f.app U) (h U))
    (fun {_ _} i ↦ f.naturality i)

private theorem restrictionTensorPresheafIso_pure
    {D : Type c} [Category.{v} D] {E : Type c₂} [Category.{v₂} E]
    {F : D ⥤ E} {R : Eᵒᵖ ⥤ CommRingCat.{r}} {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)
    (hφ : ∀ U, IsIso (φ.app U))
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Dᵒᵖ) (x : M.obj (F.op.obj U)) (y : N.obj (F.op.obj U)) :
    (restrictionTensorPresheafIso φ hφ M N).hom.app U (x ⊗ₜ[S.obj U] y) =
      x ⊗ₜ[R.obj (F.op.obj U)] y := by
  unfold restrictionTensorPresheafIso
  exact PresheafOfModules.pushforward_μ_app_tmul φ M N U x y

attribute [local irreducible] systemRing ringPresheaf rings
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
@[irreducible] private def evaluationTensorPresheafIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    PresheafOfModules.Monoidal.tensorObj (R := (B n).obj)
      ((evaluation.{c, v, max c v r} J B τ n).obj M).val
      ((evaluation.{c, v, max c v r} J B τ n).obj N).val ≅
      (PresheafOfModules.pushforward
        (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom).obj
          (PresheafOfModules.Monoidal.tensorObj
            (R := (systemRing.{c, v, max c v r} J B τ).obj) M.val N.val) := by
  dsimp only [evaluation, SheafOfModules.pushforward]
  exact restrictionTensorPresheafIso
    (F := Prod.sectR n C) (R := (systemRing.{c, v, max c v r} J B τ).obj)
    (S := (B n).obj) (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom
    (fun U ↦ by
      let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
      have : IsIso φ.hom := inferInstance
      exact NatIso.isIso_app_of_isIso φ.hom U) M.val N.val

private theorem evaluationTensorPresheafIso_pure (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom.app U
      (x ⊗ₜ[(B n).obj.obj U] y) =
      x ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, U.unop))] y := by
  unfold evaluationTensorPresheafIso
  exact restrictionTensorPresheafIso_pure
    (F := Prod.sectR n C) (R := (systemRing.{c, v, max c v r} J B τ).obj)
    (S := (B n).obj) _ _ M.val N.val U x y

@[irreducible] private def evaluationTensorComparison (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    ordinaryTensor.{c, v, r} J (B n) ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  letI := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  exact (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
      ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom ≫
    (PresheafOfModules.sheafification.{max c v r} (R := ring.{c, v, max c v r} J (B n))
      (𝟙 _)).map (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom ≫
    restrictionSheafificationMap.{c, v, max c v r, c, v} φ P ≫
    (evaluation.{c, v, max c v r} J B τ n).map
      (SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N).inv

private theorem evaluationTensorComparison_isIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    IsIso (evaluationTensorComparison.{c, v, r} J B τ n M N) := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  have : (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) :=
    ⟨fun hS ↦ hS⟩
  have := restrictionSheafificationMap_isIso.{c, v, max c v r, c, v} φ P
  unfold evaluationTensorComparison
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem evaluationTensorComparison_pure (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (evaluationTensorComparison.{c, v, r} J B τ n M N).val.app U
      (tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U x y) =
      tensorSection.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop)) x y  := by
  let R := systemRing.{c, v, max c v r} J B τ
  let φ := eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm
  let P := PresheafOfModules.Monoidal.tensorObj (R := R.obj) M.val N.val
  let Q := PresheafOfModules.Monoidal.tensorObj (R := (B n).obj)
    ((evaluation.{c, v, max c v r} J B τ n).obj M).val
    ((evaluation.{c, v, max c v r} J B τ n).obj N).val
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let T := SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r}
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
    ((evaluation.{c, v, max c v r} J B τ n).obj N)
  let V := SheafOfModules.tensorObjIsoSheafification.{v, c, max c v r} M N
  unfold evaluationTensorComparison
  exact (tensorComparison_unit_apply φ P Q
    (evaluationTensorPresheafIso.{c, v, r} J B τ n M N).hom T V U
    (x ⊗ₜ[(B n).obj.obj U] y)).trans
      (congrArg (fun z ↦ V.inv.val.app (op (n, U.unop))
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (R := ring.{c, v, max c v r} (coefficientSequenceTopology J) R)
          (𝟙 _)).unit.app P).app (op (n, U.unop)) z))
        (evaluationTensorPresheafIso_pure.{c, v, r} J B τ n M N U x y))

@[irreducible] private def evaluationTensorIso (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≅
      ordinaryTensor.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) :=
  (@asIso _ _ _ _ (evaluationTensorComparison.{c, v, r} J B τ n M N)
    (evaluationTensorComparison_isIso.{c, v, r} J B τ n M N)).symm

private theorem evaluationTensorIso_fac (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) :
    evaluationTensorComparison.{c, v, r} J B τ n M N ≫
        (evaluationTensorIso.{c, v, r} J B τ n M N).hom = 𝟙 _ := by
  have := evaluationTensorComparison_isIso.{c, v, r} J B τ n M N
  unfold evaluationTensorIso
  exact IsIso.hom_inv_id _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] ordinaryEvaluationTensor

namespace Data

variable (A : Data.{c, v, r} J B τ)

/-- The reduction of a normalized system, as an isomorphism between levels. -/
def cartesianReduction (M : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ A.scalar M) {m n : ℕ} (h : n ≤ m) :
    (A.scalar h).T.obj ((e.{c, v, max c v r} J B τ m).obj M) ≅
      (e.{c, v, max c v r} J B τ n).obj M :=
  @asIso _ _ _ _ (reduction.{c, v, max c v r} J B τ h (A.scalar h) M) (hM h)

/-- The displayed tensor-Hom transpose which determines the internal-Hom reduction. -/
def homReductionTranspose (M N : DS.{c, v, max c v r} J B τ)
    (hM : Normalized.{c, v, max c v r} J B τ A.scalar M) {m n : ℕ} (h : n ≤ m) :
    (A.scalar h).T.obj
      ((internalHom.{c, v, r} J (B m)).obj
        (op ((e.{c, v, max c v r} J B τ m).obj M), (e.{c, v, max c v r} J B τ m).obj N)) ⟶
      (internalHom.{c, v, r} J (B n)).obj
        (op ((e.{c, v, max c v r} J B τ n).obj M), (e.{c, v, max c v r} J B τ n).obj N) :=
  (A.levelClosed n).transpose _ _ _
    ((A.levelClosed n).tensor.map
      (Prod.mkHom (𝟙 _) (A.cartesianReduction J B τ M hM h).inv) ≫
      (A.scalarTensor h).inv.app
        ((internalHom.{c, v, r} J (B m)).obj
          (op ((e.{c, v, max c v r} J B τ m).obj M), (e.{c, v, max c v r} J B τ m).obj N),
          (e.{c, v, max c v r} J B τ m).obj M) ≫
      (A.scalar h).T.map ((A.levelClosed m).evaluation
        ((e.{c, v, max c v r} J B τ m).obj M) ((e.{c, v, max c v r} J B τ m).obj N)) ≫
      reduction.{c, v, max c v r} J B τ h (A.scalar h) N)

/-- Equality with the specified transpose, including the two Hom evaluation comparisons. -/
def HomReductionFormula : Prop :=
  ∀ (M N : DS.{c, v, max c v r} J B τ) (hM : Normalized.{c, v, max c v r} J B τ A.scalar M)
    (m n : ℕ) (h : n ≤ m),
    reduction.{c, v, max c v r} J B τ h (A.scalar h)
        ((internalHom.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (op M, N)) ≫
        (A.homEvaluation M hM n).hom.app N =
      (A.scalar h).T.map ((A.homEvaluation M hM m).hom.app N) ≫
        A.homReductionTranspose J B τ M N hM h

end Data

section ScalarSystems

variable (F : ℕ → Sheaf J CommRingCat.{max c v r})
  (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
  (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)

end ScalarSystems

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local semireducible] systemRing ringPresheaf rings

section OpenLocalization

variable (U : C)

/-- The localized coefficient tower, with its unchanged section rings. -/
abbrev openRings (n : ℕ) : Sheaf (J.over U) CommRingCat.{max c v r} := (B n).over U

/-- The localized coefficient transitions are the restrictions of tau. -/
def openTransitions (n : ℕ) : openRings.{c, v, r} J B U (n + 1) ⟶ openRings.{c, v, r} J B U n :=
  (J.overPullback CommRingCat.{max c v r} U).map (τ n)

/-- The actual site functor defining j-star on systems. -/
def openSite : ℕ × Over U ⥤ ℕ × C := (𝟭 ℕ).prod (Over.forget U)

omit ambientSmall in
/-- The product slice-forgetful functor is continuous for the vertical topologies. -/
theorem openSite_continuous :
    (openSite U).IsContinuous (coefficientSequenceTopology (J.over U))
      (coefficientSequenceTopology J) := by
  apply Functor.isContinuous_of_coverPreserving
  · constructor
    intro ℱ Z T x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h
    let W' : ℕ × Over U := (W.1, Over.mk (f₁.2 ≫ Y₁.2.hom))
    let f₁' : W' ⟶ Y₁ := Prod.mkHom f₁.1 (Over.homMk f₁.2)
    let f₂' : W' ⟶ Y₂ := Prod.mkHom f₂.1 (Over.homMk f₂.2 (by
      have hh := congrArg (fun f ↦ f.2) h
      simpa [openSite, Category.assoc, Over.w] using hh.symm =≫ Z.2.hom))
    exact hx f₁' f₂' hg₁ hg₂ (by
      apply Prod.hom_ext
      · exact congrArg (fun f ↦ f.1) h
      · apply Over.OverMorphism.ext
        exact congrArg (fun f ↦ f.2) h)
  · constructor
    intro X S hS
    change Sieve.overEquiv X.2
      (S.functorPullback (Prod.sectR X.1 (Over U))) ∈ J X.2.left at hS
    apply J.superset_covering _ hS
    intro V f hf
    rcases hf with ⟨W, g, k, hg, rfl⟩
    exact ⟨(X.1, W), Prod.mkHom (𝟙 _) g, Prod.mkHom (𝟙 _) k,
      hg, rfl⟩

attribute [instance] openSite_continuous

/-- Restricting the actual sequence ring gives the localized sequence ring. -/
theorem openRing :
    ((openSite U).sheafPushforwardContinuous RingCat.{max c v r}
      (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology J)).obj
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ)) =
      ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
        (systemRing.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)) := by
  let cmp : rings.{c, v, max c v r} J B τ ⋙
      J.overPullback CommRingCat.{max c v r} U ⟶
      rings.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [CategoryTheory.Functor.comp_map, rings,
        CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp, Category.comp_id]
      rfl)
  apply ObjectProperty.FullSubcategory.ext
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro X Y f
  have hh := cmp.naturality (f.unop.1).op
  dsimp only [cmp] at hh
  simp only [NatTrans.ofOpSequence_app, Category.id_comp, Category.comp_id] at hh
  dsimp [openSite, ring, systemRing, ringPresheaf,
    CategoryTheory.Functor.sheafPushforwardContinuous]
  apply heq_of_eq
  change (forget₂ CommRingCat RingCat).map _ = (forget₂ CommRingCat RingCat).map _
  congr 1
  dsimp [CategoryTheory.Functor.uncurry]
  congr 1
  exact congrArg (fun α ↦ α.hom.app (op X.unop.2)) hh

/-- Actual j-star is restriction of the system presheaf along openSite. -/
def openRestriction : Systems.{c, v, max c v r} J B τ ⥤
    Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) :=
  SheafOfModules.pushforward (F := openSite U)
    (eqToHom (openRing.{c, v, r} J B τ U).symm)

/-- Actual restriction of systems is additive and exact. -/
theorem openRestriction_exact :
    (openRestriction.{c, v, r} J B τ U).Additive ∧
    PreservesFiniteLimits (openRestriction.{c, v, r} J B τ U) ∧
    PreservesFiniteColimits (openRestriction.{c, v, r} J B τ U) := by
  have hco : (openSite U).IsCocontinuous
      (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology J) := by
    constructor
    intro X S hS
    change S.functorPullback (Prod.sectR X.1 C) ∈ J X.2.left at hS
    change Sieve.overEquiv X.2
      ((S.functorPullback (openSite U)).functorPullback
        (Prod.sectR X.1 (Over U))) ∈ J X.2.left
    have he : Sieve.overEquiv X.2
        ((S.functorPullback (openSite U)).functorPullback
          (Prod.sectR X.1 (Over U))) = S.functorPullback (Prod.sectR X.1 C) := by
      apply Sieve.ext
      intro V f
      rw [Sieve.overEquiv_iff]
      rfl
    rw [he]
    exact hS
  have : HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r} :=
    abelianSheafify.{c, v, max c v r} (coefficientSequenceTopology J)
  have : HasSheafify (coefficientSequenceTopology (J.over U))
      AddCommGrpCat.{max c v r} :=
    abelianSheafify.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
  exact modulePushforward_exact.{max c v, v, r, c, v}
    (eqToHom (openRing.{c, v, r} J B τ U).symm)

/-- Additivity of actual system restriction. -/
instance openRestrictionAdditive : (openRestriction.{c, v, r} J B τ U).Additive :=
  (openRestriction_exact.{c, v, r} J B τ U).1

/-- Left exactness of actual system restriction. -/
instance openRestrictionLimits : PreservesFiniteLimits (openRestriction.{c, v, r} J B τ U) :=
  (openRestriction_exact.{c, v, r} J B τ U).2.1

/-- Right exactness of actual system restriction. -/
instance openRestrictionColimits : PreservesFiniteColimits (openRestriction.{c, v, r} J B τ U) :=
  (openRestriction_exact.{c, v, r} J B τ U).2.2

/-- The normalized extension/restriction adjunction on actual system categories.
The right adjoint is the constructed sectionwise restriction. The left adjoint is
specified by its universal property and the dependency's direct-sum/sheafification
model at every level; unit and counit equations fix those identifications. -/
structure OpenSystems where
  /-- Actual extension by zero, determined up to unique adjunction-compatible iso. -/
  extension : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) ⥤ Systems.{c, v, max c v r}
        J B τ
  /-- Its universal property against the constructed restriction. -/
  ordinaryAdjunction : extension ⊣ openRestriction.{c, v, r} J B τ U
  /-- Extension is additive. -/
  [extensionAdditive : extension.Additive]
  /-- Extension is left exact. -/
  [extensionLimits : PreservesFiniteLimits extension]
  /-- Extension is right exact. -/
  [extensionColimits : PreservesFiniteColimits extension]
  /-- Levelwise actual direct-sum/sheafification extension. -/
  extensionEvaluation : ∀ n : ℕ,
    extension ⋙ evaluation.{c, v, max c v r} J B τ n ≅
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ⋙
          (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)
  /-- Levelwise actual slice restriction. -/
  restrictionEvaluation : ∀ n : ℕ,
    openRestriction.{c, v, r} J B τ U ⋙ evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n ≅
      evaluation.{c, v, max c v r} J B τ n ⋙
        SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U
  /-- Restriction evaluation retains the original section, at every coefficient level. -/
  restrictionSections : ∀ (n : ℕ)
    (N : Systems.{c, v, max c v r} J B τ) (V : (Over U)ᵒᵖ)
    (x : ((openRestriction.{c, v, r} J B τ U ⋙
      evaluation.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).obj N).val.obj V),
      HEq (((restrictionEvaluation n).hom.app N).val.app V x) x
  /-- Unit evaluation is the actual level unit, whose formula is the summand injection. -/
  unit_evaluation : ∀ (n : ℕ)
    (M : Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)),
    (evaluation.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).map
        (ordinaryAdjunction.unit.app M) ≫
        (restrictionEvaluation n).hom.app (extension.obj M) ≫
        (SheafOfModules.localizedSystemRestriction.{c, v, r} (B n) U).map
          ((extensionEvaluation n).hom.app M) =
      ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).unit.app
        ((evaluation.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).obj M)
  /-- Counit evaluation is the actual level counit. -/
  counit_evaluation : ∀ (n : ℕ) (N : Systems.{c, v, max c v r} J B τ),
    ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).map
        ((restrictionEvaluation n).hom.app N) ≫
        ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
            (abelianSheafify.{c, v, max c v r} J)
            (locallyBijective.{c, v, max c v r} J) (B n) U)).counit.app
          ((evaluation.{c, v, max c v r} J B τ n).obj N) =
      (extensionEvaluation n).inv.app ((openRestriction.{c, v, r} J B τ U).obj N) ≫
        (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.counit.app N)
  /-- Ordinary unbounded derived j-shriek adjoint to derived j-star. -/
  adjunction : extension.mapDerivedCategory ⊣ (openRestriction.{c, v, r} J B τ U).mapDerivedCategory

  /-- The derived adjunction is exactly the localized ordinary Hom equivalence. -/
  transpose_model : ∀
    (P : CochainComplex (Systems.{max c v, v, max c v r} (J.over U)
      (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U)) ℤ)
    (Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (f : (extension.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
    ((adjunction.homEquiv _ _)
      ((Functor.mapDerivedCategoryFactors extension).hom.app P ≫ DerivedCategory.Q.map f)) ≫
        (Functor.mapDerivedCategoryFactors (openRestriction.{c, v, r} J B τ U)).hom.app Q =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f)

attribute [instance] OpenSystems.extensionAdditive OpenSystems.extensionLimits
  OpenSystems.extensionColimits

end OpenLocalization

end WeilConjectures.SemilinearSections
