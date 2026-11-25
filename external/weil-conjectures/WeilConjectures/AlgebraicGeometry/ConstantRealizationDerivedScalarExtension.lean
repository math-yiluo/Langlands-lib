/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.AB
/-!
# Derived constant realization and scalar extension

Source: Stacks Project, Cohomology on Sites, Tags 0G7E and 0D6D; Modules on Sites,
Tags 093J, 0GMW and 03CY (auxiliary; not a blueprint node).
Scalar extension is the left adjoint to actual restriction; its universal property
fixes the construction up to the unique unit-preserving isomorphism. The comparison
below is its mate, not a choice of an unspecified natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512

universe u v wR wS wT dR dS dT r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory.ConstantScalarRealization

-- Chosen left adjoints are used through their adjunction, without reducing the choice.
attribute [local irreducible] Functor.leftAdjoint

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R S : Type (max u v)} [CommRing R] [CommRing S] (q : R →+* S)

/-- Actual restriction along the constant coefficient map.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
def restriction : realizationModules J S ⥤ realizationModules J R :=
  SheafOfModules.restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)))

/-- Actual restriction is additive.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance restriction_additive : (restriction J q).Additive := by
  unfold restriction
  infer_instance

/-- Restriction is exact and has the ordinary sheafified tensor as left adjoint.
Source: Stacks 03DA and 07A6
(auxiliary; not a blueprint node).
Proof: restriction retains the underlying abelian sheaf, so kernels and sheafified
cokernels are unchanged. Its left adjoint is sectionwise scalar tensor followed by
module sheafification; the tensor and sheafification universal properties give the
adjunction. This is the identity-site specialization of derived change of rings. -/
theorem restriction_properties :
    PreservesFiniteLimits (restriction J q) ∧
      PreservesFiniteColimits (restriction J q) ∧ (restriction J q).IsRightAdjoint := by
  let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
  have : PreservesFiniteLimits (restriction J q ⋙ SheafOfModules.toSheaf _) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J S))))
  have : PreservesFiniteColimits (restriction J q ⋙ SheafOfModules.toSheaf _) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J S))))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _),
    preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _),
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction φ).isRightAdjoint⟩

/-- Exactness of actual restriction.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance restriction_limits : PreservesFiniteLimits (restriction J q) :=
  (restriction_properties J q).1

/-- Exactness of actual restriction.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance restriction_colimits : PreservesFiniteColimits (restriction J q) :=
  (restriction_properties J q).2.1

/-- The ordinary scalar adjunction exists by its tensor universal property.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance restriction_rightAdjoint : (restriction J q).IsRightAdjoint :=
  (restriction_properties J q).2.2

/-- Actual ordinary extension, determined by the tensor universal property.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
abbrev extension := (restriction J q).leftAdjoint

/-- The scalar tensor/restriction adjunction.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
def adjunction : extension J q ⊣ restriction J q := Adjunction.ofIsRightAdjoint _

/-- Tensor extension is additive since restriction is additive.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance extension_additive : (extension J q).Additive :=
  (adjunction J q).left_adjoint_additive

/-- Additivity of ordinary module scalar extension.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
instance moduleExtension_additive {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{r, r, r} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

/-- A constant section, from the module-sheafification unit.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def constantSection (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).obj M).val.obj V :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V) x

private theorem constantSection_eq (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) (x : M) :
    constantSection J M V x =
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf).app V x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact ConcreteCategory.congr_hom
    (congr_app (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (realizationRingUnit J R) ((siteConstantModulePresheafGeneral (C := C) R).obj M)) V) x

private theorem realizationRingUnit_naturality (V : Cᵒᵖ) (a : R) :
    (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q))).hom.app V)
        ((realizationRingUnit J R).app V a) =
      (realizationRingUnit J S).app V (q a) := by
  have h := toSheafify_naturality (D := CommRingCat.{max u v}) J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom q))
  exact (ConcreteCategory.congr_hom (congr_app h V) a).symm

private def restrictionSeed (M : ModuleCat.{max u v} S) :
    (siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J R)).obj
        ((restriction J q).obj ((commutativeSiteConstantModuleFunctor J S).obj M)).val := by
  let := (realizationRingUnit_locallyBijective J S).1
  let := (realizationRingUnit_locallyBijective J S).2
  let P := (siteConstantModulePresheafGeneral (C := C) S).obj M
  let τ := PresheafOfModules.toSheafify (realizationRingUnit J S)
    (toSheafify J P.presheaf)
  refine PresheafOfModules.homMk (toSheafify J P.presheaf) ?_
  intro V a x
  refine ((τ.app V).hom.map_smul (q a) x).trans ?_
  exact congrArg
    (fun t : (realizationRing J S).obj.obj V ↦
      t • (show ((commutativeSiteConstantModuleFunctor J S).obj M).val.obj V
        from τ.app V x))
    (realizationRingUnit_naturality J q V a).symm

private theorem restrictionSeed_toPresheaf (M : ModuleCat.{max u v} S) :
    (PresheafOfModules.toPresheaf _).map (restrictionSeed J q M) =
      toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf := by
  ext V x
  rfl

attribute [local irreducible] restrictionSeed

private def restrictionComparison (M : ModuleCat.{max u v} S) :
    (commutativeSiteConstantModuleFunctor J R).obj ((ModuleCat.restrictScalars q).obj M) ⟶
      (restriction J q).obj ((commutativeSiteConstantModuleFunctor J S).obj M) :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R)).symm
    (restrictionSeed J q M)

attribute [local irreducible] restrictionComparison

private theorem restrictionComparison_transpose (M : ModuleCat.{max u v} S) :
    letI := (realizationRingUnit_locallyBijective J R).1
    letI := (realizationRingUnit_locallyBijective J R).2
    (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R))
      (restrictionComparison J q M) = restrictionSeed J q M := by
  unfold restrictionComparison
  exact Equiv.apply_symm_apply _ _

private theorem restrictionComparison_fac (M : ModuleCat.{max u v} S) :
    toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf ≫
      ((SheafOfModules.toSheaf _).map (restrictionComparison J q M)).hom =
        (PresheafOfModules.toPresheaf _).map (restrictionSeed J q M) := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  change toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
      ((ModuleCat.restrictScalars q).obj M)).presheaf ≫
    (PresheafOfModules.toPresheaf _).map (restrictionComparison J q M).val = _
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  exact congrArg (PresheafOfModules.toPresheaf _).map
    (restrictionComparison_transpose J q M)

private theorem isIso_of_local_generators
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {A B : Sheaf J AddCommGrpCat.{max u v}}
    (f : P ⟶ A.obj) [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f]
    (g : P ⟶ B.obj) [Presheaf.IsLocallyInjective J g]
    [Presheaf.IsLocallySurjective J g] (h : A ⟶ B) (fac : f ≫ h.hom = g) :
    IsIso h := by
  apply (Sheaf.isLocallyBijective_iff_isIso h).mp
  have hi : Presheaf.IsLocallyInjective J (f ≫ h.hom) := by
    rw [fac]
    infer_instance
  have hs : Presheaf.IsLocallySurjective J (f ≫ h.hom) := by
    rw [fac]
    infer_instance
  exact ⟨(Presheaf.comp_isLocallyInjective_iff J f h.hom).mp hi,
    (Presheaf.comp_isLocallySurjective_iff J f h.hom).mp hs⟩

private theorem restrictionComparison_isIso (M : ModuleCat.{max u v} S) :
    IsIso (restrictionComparison J q M) := by
  let P := (siteConstantModulePresheafGeneral (C := C) R).obj
    ((ModuleCat.restrictScalars q).obj M)
  have hi : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M)) := by
    rw [restrictionSeed_toPresheaf]
    exact (J.W_toSheafify _).isLocallyInjective
  have hs : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M)) := by
    rw [restrictionSeed_toPresheaf]
    exact (J.W_toSheafify _).isLocallySurjective
  let := hi
  let := hs
  have : IsIso ((SheafOfModules.toSheaf _).map (restrictionComparison J q M)) :=
    isIso_of_local_generators J (toSheafify J P.presheaf)
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M))
      ((SheafOfModules.toSheaf _).map (restrictionComparison J q M))
      (restrictionComparison_fac J q M)
  exact isIso_of_reflects_iso (restrictionComparison J q M) (SheafOfModules.toSheaf _)

private theorem constantSection_naturality {M N : ModuleCat.{max u v} R}
    (f : M ⟶ N) (V : Cᵒᵖ) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).map f).val.app V
      (constantSection J M V x) = constantSection J N V (f x) := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  have h := (PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit J R)).unit.naturality
      ((siteConstantModulePresheafGeneral (C := C) R).map f)
  exact (congrArg (fun t ↦ t.app V x) h).symm

private theorem constantSection_ext {M : ModuleCat.{max u v} R}
    {N : realizationModules J R}
    {f g : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ N}
    (h : ∀ (V : Cᵒᵖ) (x : M),
      f.val.app V (constantSection J M V x) = g.val.app V (constantSection J M V x)) :
    f = g := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  apply (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R)).injective
  ext V x
  exact h V x

private theorem restrictionComparison_constantSection (M : ModuleCat.{max u v} S)
    (V : Cᵒᵖ) (x : M) :
    (restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x) =
      constantSection J M V x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (restrictionComparison_fac J q M) V) x
  change (restrictionComparison J q M).val.app V
      ((toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf).app V x) =
      (restrictionSeed J q M).app V x at h
  rw [constantSection_eq, constantSection_eq]
  exact h.trans (by unfold restrictionSeed; rfl)

/-- Restricting constant realization commutes canonically with restricting modules.
The equation fixes the comparison on constant presheaf sections.
Source: Stacks 03CY (auxiliary; not a blueprint node).
Proof: the two sheafifications have the same underlying abelian sheaf and the same
restricted R-action on constant sections. The universal property of sheafification
extends the identity to a unique linear isomorphism; the same uniqueness gives
naturality in M. Constant sections locally generate, so the equation gives uniqueness. -/
theorem restrictionIso_existsUnique :
    ∃! e : commutativeSiteConstantModuleFunctor J S ⋙ restriction J q ≅
        ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R,
      ∀ (M : ModuleCat.{max u v} S) (V : Cᵒᵖ) (x : M),
        (e.hom.app M).val.app V (constantSection J M V x) =
          constantSection J ((ModuleCat.restrictScalars q).obj M) V x := by
  have hIso (M : ModuleCat.{max u v} S) : IsIso (restrictionComparison J q M) :=
    restrictionComparison_isIso J q M
  let e : ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R ≅
      commutativeSiteConstantModuleFunctor J S ⋙ restriction J q :=
    NatIso.ofComponents (fun M ↦ asIso (restrictionComparison J q M)) (by
      intro M N f
      apply constantSection_ext J
      intro V x
      change (restrictionComparison J q N).val.app V
          (((commutativeSiteConstantModuleFunctor J R).map
            ((ModuleCat.restrictScalars q).map f)).val.app V
              (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) =
        ((commutativeSiteConstantModuleFunctor J S).map f).val.app V
          ((restrictionComparison J q M).val.app V
            (constantSection J ((ModuleCat.restrictScalars q).obj M) V x))
      rw [constantSection_naturality, restrictionComparison_constantSection,
        restrictionComparison_constantSection, constantSection_naturality]
      rfl)
  have he (M : ModuleCat.{max u v} S) (V : Cᵒᵖ) (x : M) :
      (e.inv.app M).val.app V (constantSection J M V x) =
        constantSection J ((ModuleCat.restrictScalars q).obj M) V x := by
    rw [← restrictionComparison_constantSection J q M V x]
    exact congrArg (fun t ↦ t.val.app V
      (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) (e.hom_inv_id_app M)
  refine ⟨e.symm, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (e.hom.app M)).mp
  change restrictionComparison J q M ≫ e'.hom.app M =
    restrictionComparison J q M ≫ e.inv.app M
  apply constantSection_ext J
  intro V x
  change (e'.hom.app M).val.app V
      ((restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) =
    (e.inv.app M).val.app V
      ((restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x))
  rw [restrictionComparison_constantSection, he', he]

/-- The identity-on-constant-sections restriction comparison.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def restrictionIso :
    commutativeSiteConstantModuleFunctor J S ⋙ restriction J q ≅
      ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R :=
  Classical.choose (restrictionIso_existsUnique J q)

/-- The ordinary comparison, defined by the scalar adjunction mate.
Source: Stacks 0GMW (auxiliary; not a blueprint node). -/
def moduleComparison (M : ModuleCat.{max u v} R) :
    (extension J q).obj ((commutativeSiteConstantModuleFunctor J R).obj M) ⟶
      (commutativeSiteConstantModuleFunctor J S).obj ((ModuleCat.extendScalars q).obj M) :=
  ((adjunction J q).homEquiv _ _).symm
    ((commutativeSiteConstantModuleFunctor J R).map
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) ≫
        (restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M))

/-- Naturality of the ordinary mate.
Source: Stacks 0GMW (auxiliary; not a blueprint node).
Proof: transpose both sides; naturality of the ordinary unit and of restrictionIso
identifies their transposes, and the adjunction Hom equivalence is injective. -/
theorem moduleComparison_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (extension J q).map ((commutativeSiteConstantModuleFunctor J R).map f) ≫
        moduleComparison J q N =
      moduleComparison J q M ≫
        (commutativeSiteConstantModuleFunctor J S).map ((ModuleCat.extendScalars q).map f) := by
  apply ((adjunction J q).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [moduleComparison, Equiv.apply_symm_apply]
  rw [← Category.assoc]
  rw [← (commutativeSiteConstantModuleFunctor J R).map_comp]
  rw [← (ModuleCat.extendRestrictScalarsAdj q).unit_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (restrictionIso J q).inv.naturality ((ModuleCat.extendScalars q).map f)

private theorem constantSection_smul (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (a : R) (x : M) :
    constantSection J M V (a • x) =
      (realizationRingUnit J R).app V a • constantSection J M V x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_smul a x

private theorem constantSection_add (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x y : M) :
    constantSection J M V (x + y) = constantSection J M V x + constantSection J M V y := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_add x y

private theorem constantSection_map (M : ModuleCat.{max u v} R)
    {V W : Cᵒᵖ} (i : V ⟶ W) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).obj M).val.map i
      (constantSection J M V x) = constantSection J M W x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
      ((siteConstantModulePresheafGeneral (C := C) R).obj M)) i x).symm

private def transposeGenerator {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) :
    M ⟶ (ModuleCat.restrictScalars q).obj
      ((ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V)) :=
  ModuleCat.ofHom
    (X := M) (Y := (ModuleCat.restrictScalars q).obj
      ((ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V)))
    { toFun := fun x ↦ f.val.app V (constantSection J M V x)
      map_add' := fun x y ↦ by rw [constantSection_add, map_add]
      map_smul' := fun a x ↦ by
        rw [constantSection_smul, map_smul]
        exact congrArg (fun t : (realizationRing J S).obj.obj V ↦
          t • (show N.val.obj V from f.val.app V (constantSection J M V x)))
          (realizationRingUnit_naturality J q V a) }

private def tensorSection {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) :
    (ModuleCat.extendScalars q).obj M ⟶
      (ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V) :=
  ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).symm (transposeGenerator J q f V)

private theorem tensorSection_one {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (x : M) :
    tensorSection J q f V ((1 : S) ⊗ₜ[R, q] x) =
      f.val.app V (constantSection J M V x) := by
  have h := ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).apply_symm_apply
    (transposeGenerator J q f V)
  have hx := congrArg (fun t ↦ t x) h
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hx
  exact hx

private def tensorLiftPresheaf {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N) :
    (siteConstantModulePresheafGeneral (C := C) S).obj ((ModuleCat.extendScalars q).obj M) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J S)).obj N.val where
  app V := tensorSection J q f V
  naturality {V W} i := by
    let T := (PresheafOfModules.restrictScalars (realizationRingUnit J S)).obj N.val
    change tensorSection J q f W = tensorSection J q f V ≫ T.map i
    apply ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    ext x
    change tensorSection J q f W ((1 : S) ⊗ₜ[R, q] x) =
      T.map i (tensorSection J q f V ((1 : S) ⊗ₜ[R, q] x))
    rw [tensorSection_one, tensorSection_one]
    exact (congrArg (fun t ↦ f.val.app W t) (constantSection_map J M i x)).symm.trans
      (PresheafOfModules.naturality_apply f.val i (constantSection J M V x))

private def tensorLift {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N) :
    (commutativeSiteConstantModuleFunctor J S).obj ((ModuleCat.extendScalars q).obj M) ⟶ N :=
  letI := (realizationRingUnit_locallyBijective J S).1
  letI := (realizationRingUnit_locallyBijective J S).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J S)).symm
    (tensorLiftPresheaf J q f)

private theorem tensorLift_constantSection
    {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (z : (ModuleCat.extendScalars q).obj M) :
    (tensorLift J q f).val.app V
        (constantSection J ((ModuleCat.extendScalars q).obj M) V z) =
      tensorSection J q f V z := by
  let := (realizationRingUnit_locallyBijective J S).1
  let := (realizationRingUnit_locallyBijective J S).2
  have h := (PresheafOfModules.sheafificationHomEquiv
    (realizationRingUnit J S)).apply_symm_apply (tensorLiftPresheaf J q f)
  exact congrArg (fun t ↦ t.app V z) h

private theorem restrictionIso_inv_constantSection (M : ModuleCat.{max u v} S)
    (V : Cᵒᵖ) (x : M) :
    ((restrictionIso J q).inv.app M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x) =
      constantSection J M V x := by
  have h := (Classical.choose_spec (restrictionIso_existsUnique J q)).1 M V x
  change ((restrictionIso J q).hom.app M).val.app V (constantSection J M V x) = _ at h
  rw [← h]
  exact congrArg (fun t ↦ t.val.app V (constantSection J M V x))
    ((restrictionIso J q).hom_inv_id_app M)

private theorem moduleComparison_unit_section (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x : M) :
    (moduleComparison J q M).val.app V
      (((adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
          (constantSection J M V x)) =
      constantSection J ((ModuleCat.extendScalars q).obj M) V ((1 : S) ⊗ₜ[R, q] x) := by
  have h : (adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M) ≫
      (restriction J q).map (moduleComparison J q M) =
    (commutativeSiteConstantModuleFunctor J R).map
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) ≫
      (restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M) := by
    exact ((adjunction J q).homEquiv_unit _ _ (moduleComparison J q M)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hx := congrArg (fun t ↦ t.val.app V (constantSection J M V x)) h
  change (moduleComparison J q M).val.app V
      (((adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
          (constantSection J M V x)) =
    ((restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M)).val.app V
      (((commutativeSiteConstantModuleFunctor J R).map
        ((ModuleCat.extendRestrictScalarsAdj q).unit.app M)).val.app V
          (constantSection J M V x)) at hx
  refine hx.trans ?_
  refine (congrArg
    (fun z ↦ ((restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M)).val.app V z)
    (constantSection_naturality J
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) V x)).trans ?_
  exact (restrictionIso_inv_constantSection J q ((ModuleCat.extendScalars q).obj M) V
    (((ModuleCat.extendRestrictScalarsAdj q).unit.app M) x)).trans
      (congrArg (constantSection J ((ModuleCat.extendScalars q).obj M) V)
        (ModuleCat.extendRestrictScalarsAdj_unit_app_apply q M x))

private theorem tensorSection_tmul {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (x : M) (s : S) :
    tensorSection J q f V (s ⊗ₜ[R, q] x) =
      (realizationRingUnit J S).app V s •
        (show N.val.obj V from f.val.app V (constantSection J M V x)) := by
  have ht : s ⊗ₜ[R, q] x = s • ((1 : S) ⊗ₜ[R, q] x :
      (ModuleCat.extendScalars q).obj M) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ht, map_smul, tensorSection_one]
  rfl

private theorem moduleComparison_formula (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x : M) (s : S) :
    (moduleComparison J q M).val.app V
      ((realizationRingUnit J S).app V s •
        (show ((extension J q).obj
          ((commutativeSiteConstantModuleFunctor J R).obj M)).val.obj V from
          ((adjunction J q).unit.app
            ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
              (constantSection J M V x))) =
      constantSection J ((ModuleCat.extendScalars q).obj M) V (s ⊗ₜ[R, q] x) := by
  rw [map_smul, moduleComparison_unit_section]
  have h := constantSection_smul J ((ModuleCat.extendScalars q).obj M) V s
    ((1 : S) ⊗ₜ[R, q] x)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at h
  exact h.symm

private theorem constantSection_zero (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) :
    constantSection J M V 0 = 0 := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_zero

private theorem moduleComparison_isIso (M : ModuleCat.{max u v} R) :
    IsIso (moduleComparison J q M) := by
  let X := (commutativeSiteConstantModuleFunctor J R).obj M
  let η := (adjunction J q).unit.app X
  let g := tensorLift J q η
  have h₁ : moduleComparison J q M ≫ g = 𝟙 _ := by
    apply ((adjunction J q).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_id]
    apply constantSection_ext J
    intro V x
    change g.val.app V ((moduleComparison J q M).val.app V
      (η.val.app V (constantSection J M V x))) = η.val.app V (constantSection J M V x)
    rw [moduleComparison_unit_section, tensorLift_constantSection, tensorSection_one]
    rfl
  have h₂ : g ≫ moduleComparison J q M = 𝟙 _ := by
    apply constantSection_ext J
    intro V z
    change (moduleComparison J q M).val.app V
      (g.val.app V (constantSection J ((ModuleCat.extendScalars q).obj M) V z)) =
        constantSection J ((ModuleCat.extendScalars q).obj M) V z
    induction z using TensorProduct.inductionOn with
    | tmul s x =>
      rw [tensorLift_constantSection, tensorSection_tmul]
      exact moduleComparison_formula J q M V x s
    | add z w hz hw => rw [constantSection_add, map_add, map_add, hz, hw]
  exact ⟨⟨g, h₁, h₂⟩⟩

/-- The ordinary comparison is an isomorphism, with the identity-on-tensors formula.
Scalar-first tensors in Lean are the paper's m tensor s with factors interchanged.
Source: Stacks 0GMW and 03CY
(auxiliary; not a blueprint node).
Proof: sheafify the identity of constant presheaves with value S tensor_R M.
The tensor and sheafification universal properties identify its map with the mate
moduleComparison. The inverse is induced by the same pure tensors, so both composites
are identities. The displayed equation is the value on each constant generator. -/
theorem moduleComparison_tensor (M : ModuleCat.{max u v} R) :
    IsIso (moduleComparison J q M) ∧
      ∀ (V : Cᵒᵖ) (x : M) (s : S),
        (moduleComparison J q M).val.app V
          (((realizationRingUnit J S).app V s) •
            (@id (((extension J q).obj
                ((commutativeSiteConstantModuleFunctor J R).obj M)).val.obj V)
              (((adjunction J q).unit.app
                ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
                  (constantSection J M V x)))) =
          constantSection J ((ModuleCat.extendScalars q).obj M) V
            (s ⊗ₜ[R, q] x) := by
  exact ⟨moduleComparison_isIso J q M, moduleComparison_formula J q M⟩

/-- The genuine chain map of termwise constant tensor comparisons.
Source: Stacks 0GMW (auxiliary; not a blueprint node). -/
def complexComparison (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ((extension J q).mapHomologicalComplex (.up ℤ)).obj
        (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((commutativeSiteConstantModuleFunctor J S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) where
  f n := moduleComparison J q (P.X n)
  comm' i j _ := (moduleComparison_naturality J q (P.d i j)).symm

section SheafDerivedExistence

variable [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]

/-- Exact derived restriction of module sheaves.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
abbrev derivedRestriction := (restriction J q).mapDerivedCategory

/-- Unbounded scalar extension is left adjoint to exact restriction on module sheaves.
Source: Stacks 06YY and 07A6
(auxiliary; not a blueprint node).
Proof: derived change of rings supplies an everywhere defined left derived tensor
functor computed by K-flat resolutions. The derived adjunction theorem identifies
its right adjoint with exact restriction. Transport along the canonical equivalences
of localization universes gives the independently sized source and target. -/
@[instance] theorem derivedRestriction_isRightAdjoint :
    (derivedRestriction.{u, v, dR, dS} J q).IsRightAdjoint := by
  let Ft := derivedRestriction.{u, v, dR, dS} J q
  let QAR := @DerivedCategory.Q (realizationModules J R) _ _
    (inferInstance : HasDerivedCategory.{dR} (realizationModules J R))
  let QBS := @DerivedCategory.Q (realizationModules J S) _ _
    (inferInstance : HasDerivedCategory.{dS} (realizationModules J S))
  let hA := HasDerivedCategory.standard (realizationModules J R)
  let hB := HasDerivedCategory.standard (realizationModules J S)
  let := hA
  let := hB
  let QA := @DerivedCategory.Q _ _ _ hA
  let QB := @DerivedCategory.Q _ _ _ hB
  let WA := HomologicalComplex.quasiIso (realizationModules J R) (.up ℤ)
  let WB := HomologicalComplex.quasiIso (realizationModules J S) (.up ℤ)
  let eA := Localization.uniq QA (QAR) WA
  let eB := Localization.uniq QB (QBS) WB
  let F := @Functor.mapDerivedCategory _ _ _ hB _ _ _ hA
    (restriction J q) _ _ _
  have : F.IsRightAdjoint := by
    let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
    obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction φ
    obtain ⟨E, hobj, hmap, hadd, _, _, LF, ε, hLF, _⟩ :=
      SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
    let := hadd
    obtain ⟨_, _, hd⟩ := h E hobj hmap
    obtain ⟨d, _⟩ := hd LF ε hLF
    exact d.isRightAdjoint
  let G := (eB.inverse ⋙ F) ⋙ eA.functor
  have : G.IsRightAdjoint := inferInstance
  let H := (restriction J q).mapHomologicalComplex (.up ℤ)
  let e : QBS ⋙ G ≅ H ⋙ QAR :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Localization.compUniqInverse QB
          (QBS) WB) F) eA.functor ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors _ _ _ hB _ _ _ hA
          (restriction J q) _ _ _) eA.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H
        (Localization.compUniqFunctor QA (QAR) WA)
  let : Localization.Lifting QBS WB
      (H ⋙ QAR) G := ⟨e⟩
  let i : Ft ≅ G :=
    Localization.liftNatIso QBS WB (H ⋙ QAR) (H ⋙ QAR) Ft G (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso i.symm

end SheafDerivedExistence

section Derived

variable [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]
  [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]

/-- Exact derived restriction of ordinary modules at independent localization sizes.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
abbrev moduleDerivedRestriction {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :=
  (ModuleCat.restrictScalars.{r} f).mapDerivedCategory

/-- Unbounded scalar extension is left adjoint to exact restriction on modules.
Source: Stacks 06YY and 07A6
(auxiliary; not a blueprint node).
Proof: apply derived change of rings on the one-object identity-covering site,
whose module category is ordinary modules. K-flat resolutions compute its everywhere
defined left derived functor. The derived adjunction theorem identifies exact
restriction as its right adjoint, for any independently chosen localization sizes. -/
instance moduleDerivedRestriction_rightAdjoint
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    (moduleDerivedRestriction.{wR, wS, r} f).IsRightAdjoint := by
  let Ft := moduleDerivedRestriction.{wR, wS, r} f
  let QAR := @DerivedCategory.Q (ModuleCat.{r} A) _ _
    (inferInstance : HasDerivedCategory.{wR} (ModuleCat.{r} A))
  let QBS := @DerivedCategory.Q (ModuleCat.{r} B) _ _
    (inferInstance : HasDerivedCategory.{wS} (ModuleCat.{r} B))
  let hA := HasDerivedCategory.standard (ModuleCat.{r} A)
  let hB := HasDerivedCategory.standard (ModuleCat.{r} B)
  let := hA
  let := hB
  let QA := @DerivedCategory.Q _ _ _ hA
  let QB := @DerivedCategory.Q _ _ _ hB
  let WA := HomologicalComplex.quasiIso (ModuleCat.{r} A) (.up ℤ)
  let WB := HomologicalComplex.quasiIso (ModuleCat.{r} B) (.up ℤ)
  let eA := Localization.uniq QA (QAR) WA
  let eB := Localization.uniq QB (QBS) WB
  let F := @Functor.mapDerivedCategory _ _ _ hB _ _ _ hA
    (ModuleCat.restrictScalars f) _ _ _
  have : F.IsRightAdjoint := ModuleCat.derivedRestrictScalars_isRightAdjoint f
  let G := (eB.inverse ⋙ F) ⋙ eA.functor
  have : G.IsRightAdjoint := inferInstance
  let H := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let e : QBS ⋙ G ≅ H ⋙ QAR :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Localization.compUniqInverse QB
          (QBS) WB) F) eA.functor ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors _ _ _ hB _ _ _ hA
          (ModuleCat.restrictScalars f) _ _ _) eA.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H
        (Localization.compUniqFunctor QA (QAR) WA)
  let : Localization.Lifting QBS WB
      (H ⋙ QAR) G := ⟨e⟩
  let i : Ft ≅ G :=
    Localization.liftNatIso QBS WB (H ⋙ QAR) (H ⋙ QAR) Ft G (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso i.symm

/-- Derived scalar tensor of ordinary modules, fixed by its adjunction.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def moduleDerivedExtension {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} A) ⥤ DerivedCategory (ModuleCat.{r} B) :=
  (moduleDerivedRestriction.{wR, wS, r} f).leftAdjoint

/-- Derived scalar tensor of module sheaves, fixed by its adjunction.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def derivedExtension :
    DerivedCategory (realizationModules J R) ⥤ DerivedCategory (realizationModules J S) :=
  (derivedRestriction.{u, v, dR, dS} J q).leftAdjoint

/-- The unbounded scalar adjunction for ordinary modules.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def moduleDerivedAdjunction {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    moduleDerivedExtension.{wR, wS, r} f ⊣ moduleDerivedRestriction.{wR, wS, r} f :=
  Adjunction.ofIsRightAdjoint _

/-- The unbounded scalar adjunction for sheaves.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
def derivedAdjunction : derivedExtension.{u, v, dR, dS} J q ⊣
    derivedRestriction.{u, v, dR, dS} J q := Adjunction.ofIsRightAdjoint _

/-- Canonical ordinary-module representative map, the transpose of the localized unit.
Source: Stacks 06YY and 07A6
(auxiliary; not a blueprint node). -/
def moduleRepresentative {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] (P : CochainComplex (ModuleCat.{r} A) ℤ) :
    (moduleDerivedExtension.{wR, wS, r} f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((moduleDerivedAdjunction.{wR, wS, r} f).homEquiv _ _).symm
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ModuleCat.extendRestrictScalarsAdj f).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f))
              (.up ℤ)).inv.app P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] adjunction derivedExtension moduleDerivedExtension
  derivedAdjunction moduleDerivedAdjunction

private theorem moduleRepresentative_isIso
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    (P : CochainComplex (ModuleCat.{r} A) ℤ) (hP : P.IsKFlatForTotalTensor) :
    IsIso (moduleRepresentative.{wR, wS, r} f P) := by
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse A
  have := ModuleCat.extendScalars_preservesKFlatQuasiIso f
  have : AB5OfSize.{0, 0} (ModuleCat.{r} A) :=
    AB5OfSize_of_univLE.{0, 0, r, r} _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} A) := inferInstance
  exact Adjunction.isIso_cochainTranspose_of_kFlat
    (ModuleCat.extendScalars f) (ModuleCat.restrictScalars f)
    (ModuleCat.extendRestrictScalarsAdj f)
    (moduleDerivedAdjunction.{wR, wS, r} f) P hP

end Derived
section Tower

variable {T : Type (max u v)} [CommRing T] (b : S →+* T)

variable [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]
  [HasDerivedCategory.{wT} (ModuleCat.{max u v} T)]
  [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]
  [HasDerivedCategory.{dT} (realizationModules J T)]

end Tower
end CategoryTheory.ConstantScalarRealization
