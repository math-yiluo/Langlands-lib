/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
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
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Group.Action.Basic

/-! # The orthogonality test for local principal completeness

Source: Stacks Tags 091Q and 0999.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.ConstantCompletion

set_option synthInstance.maxSize 4096
attribute [local instance] HasDerivedCategory.standard

private theorem hom_zero_of_orthogonal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (n : ℕ) (M L : D R)
    (hM : ∀ V : D R, IsIso (n • 𝟙 V) → Subsingleton (V ⟶ M))
    (hL : IsIso (n • 𝟙 L)) :
    IsZero ((derivedInternalHom J R).obj (op L, M)) := by
  let := HasDerivedCategory.standard (Mod R)
  obtain ⟨S, hS, T, hT⟩ := RingedDerivedNative.closedAdjunction.{u, u, u, u + 1} J R
  let := S.monoidal
  let : SymmetricCategory (D R) := by
    change @SymmetricCategory (D R) _ S.monoidal
    rw [hS]
    exact RingedDerivedNative.symmetric.{u, u, u, u + 1} J R
  have hadd (X : D R) : (tensorRight X).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      (S.adjunction X).leftAdjoint_preservesColimits
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hleft (X : D R) : (tensorLeft X).Additive := by
    have := hadd X
    exact Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X).symm
  let H := (derivedInternalHom J R).obj (op L, M)
  have := hleft H
  have := hL
  have hi : IsIso (n • 𝟙 ((tensorRight L).obj H)) := by
    have h : (tensorLeft H).map (n • 𝟙 L) = n • 𝟙 ((tensorRight L).obj H) := by
      rw [Functor.map_nsmul, Functor.map_id]
      rfl
    rw [← h]
    infer_instance
  have := hM ((tensorRight L).obj H) hi
  have hh : Subsingleton (H ⟶ H) := ((S.adjunction L).homEquiv H M).symm.subsingleton
  exact (IsZero.iff_id_eq_zero _).mpr (hh.elim _ _)

private theorem restricted_orthogonal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (n : ℕ) (M : D R)
    (hM : ∀ V : D R, IsIso (n • 𝟙 V) → Subsingleton (V ⟶ M)) (U : C) :
    ∀ V : D (R.over U), IsIso (n • 𝟙 V) →
      Subsingleton (V ⟶ (ringedDerivedRestriction R U).obj M) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod (R.over U))
  let F := SheafOfModules.overFunctor (siteModuleRings R) U
  obtain ⟨G, hGlim, hGcolim, ⟨adj⟩⟩ := localized_restriction_extension_exists
    (siteModuleRings R) U (inferInstance : F.PreservesZeroMorphisms)
  have := hGlim
  have := hGcolim
  have : G.Additive := adj.left_adjoint_additive
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let da := (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    G.mapDerivedCategory F.mapDerivedCategory
  intro V hV
  have := hV
  have hi : IsIso (n • 𝟙 (G.mapDerivedCategory.obj V)) := by
    rw [← Functor.map_id G.mapDerivedCategory, ← Functor.map_nsmul]
    infer_instance
  have := hM (G.mapDerivedCategory.obj V) hi
  exact (da.homEquiv V M).symm.subsingleton

private theorem localization_nsmul_iso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (n : ℕ)
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (hs : ∀ X : Cᵒᵖ, ∃ a : R.obj.obj X, s.val X = (n : R.obj.obj X) * a) :
    IsIso (n • 𝟙 (ringedSectionLocalization R s)) := by
  let P := ringedSectionLocalizationPresheaf R s
  let T : PresheafOfModules.{u} (siteModuleRings R).obj ⥤
      Cᵒᵖ ⥤ AddCommGrpCat.{u} := PresheafOfModules.toPresheaf _
  have hiT : IsIso (T.map (n • 𝟙 P)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have he : (T.map (n • 𝟙 P)).app X = n • 𝟙 ((T.obj P).obj X) := by
      rw [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_id]
      rfl
    rw [he]
    change Function.Bijective (fun x : ringedSectionLocalizationCarrier R s X ↦ n • x)
    obtain ⟨a, ha⟩ := hs X
    have hu := IsLocalization.Away.algebraMap_isUnit
      (R := R.obj.obj X) (S := ringedSectionLocalizationCarrier R s X) (s.val X)
    have heq : algebraMap (R.obj.obj X) (ringedSectionLocalizationCarrier R s X)
        (s.val X) = (n : ringedSectionLocalizationCarrier R s X) *
          algebraMap (R.obj.obj X) (ringedSectionLocalizationCarrier R s X) a := by
      calc
        _ = algebraMap (R.obj.obj X) (ringedSectionLocalizationCarrier R s X)
            ((n : R.obj.obj X) * a) := congrArg
              (algebraMap (R.obj.obj X) (ringedSectionLocalizationCarrier R s X)) ha
        _ = _ := by rw [map_mul, map_natCast]
    have hu' : IsUnit ((n : ringedSectionLocalizationCarrier R s X) *
        algebraMap (R.obj.obj X) (ringedSectionLocalizationCarrier R s X) a) := heq ▸ hu
    have hn : IsUnit (n : ringedSectionLocalizationCarrier R s X) :=
      isUnit_of_mul_isUnit_left hu'
    have hb : Function.Bijective (fun x : ringedSectionLocalizationCarrier R s X ↦
        (n : ringedSectionLocalizationCarrier R s X) * x) := hn.smul_bijective
    simpa only [nsmul_eq_mul] using hb
  have hi : IsIso (n • 𝟙 P) := isIso_of_reflects_iso _ T
  let F := PresheafOfModules.sheafification (𝟙 (siteModuleRings R).obj)
  have : F.Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)).left_adjoint_additive
  change IsIso (n • 𝟙 (F.obj P))
  have h : F.map (n • 𝟙 P) = n • 𝟙 (F.obj P) := by
    rw [Functor.map_nsmul, Functor.map_id]
  rw [← h]
  infer_instance

private theorem kernel_section_divisible
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ) (U : C)
    (f : (constant J A).obj.obj (op U))
    (hf : ∃ y : (kernelIdeal (quotient J A (Ideal.span {(n : A)}) 0)).module.val.obj
      (op U), (kernelIdeal (quotient J A (Ideal.span {(n : A)}) 0)).inclusion.val.app
        (op U) y = f) :
    ∃ a : (constant J A).obj.obj (op U), f = (n : (constant J A).obj.obj (op U)) * a := by
  obtain ⟨y, hy⟩ := hf
  have hm : f ∈ (kernelIdeal (quotient J A (Ideal.span {(n : A)}) 0)).sections U := by
    rw [← hy]
    exact y.property
  rw [show (kernelIdeal (quotient J A (Ideal.span {(n : A)}) 0)).sections U =
      RingHom.ker ((quotient J A (Ideal.span {(n : A)}) 0).hom.app (op U)).hom from
        (kernelIdeal_existsUnique _).exists.choose_spec U,
    ((flat_and_quotients J A (Ideal.span {(n : A)})).2.2 0 U).2] at hm
  have hle : Ideal.span (Set.range (fun a : ↥((Ideal.span {(n : A)}) ^ (0 + 1)) ↦
      (constantSection (J := J) (a : A)).val (op U))) ≤
      Ideal.span {(n : (constant J A).obj.obj (op U))} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have ha : (n : A) ∣ (a : A) := Ideal.mem_span_singleton.mp (by
      simpa only [zero_add, pow_one] using a.property)
    obtain ⟨b, hb⟩ := ha
    change (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app
      (op U) a.val ∈ _
    rw [hb, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  exact Ideal.mem_span_singleton.mp (hle hm)

/-- Orthogonality against complexes on which the generator acts invertibly implies
local completeness for the principal constant ideal.

Source: Stacks Tags 091Q and 0999.
(blueprint: lem-sfb-constant-principal-complete-orthogonality).

Proof: the kernel of the constant quotient is the ideal sheaf generated by n.
For each site object U, localization at n on the slice is the telescope of
multiplication by n on its free rank-one module. The local internal-Hom condition
is the vanishing of Hom from these localized free generators and all their shifts.
Extension by zero from a slice is exact and carries these generators to objects
on which n is invertible. Thus global orthogonality implies the local vanishing
condition for n. Any local ideal section f is locally n times a section; inverting
f inverts n, so its localization satisfies the same vanishing condition. Descent
then gives local internal-Hom vanishing for every ideal section. Empty sites and
zero objects satisfy the conclusion; the regularity hypothesis is solely on the
coefficient ring. -/
theorem constantPrincipalComplete_of_orthogonal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ)
    (hn : (n : A) ∈ nonZeroDivisors A) (M : D (constant J A))
    (hM : ∀ V : D (constant J A), IsIso (n • 𝟙 V) → Subsingleton (V ⟶ M)) :
    IsComplete (quotient J A (Ideal.span {(n : A)}) 0) M := by
  -- Instead of shifted generators, test RHom(L,M) against itself by tensor-Hom adjunction.
  -- Kernel-section divisibility supplies the n-invertible localization on each slice.
  have _ := hn
  let R := constant J A
  change IsLocallyDerivedRingedIdealComplete R _ _ M
  intro U f hf
  obtain ⟨a, ha⟩ := kernel_section_divisible J A n U f hf
  let s := ringedSliceSection R U f
  have hs (X : (Over U)ᵒᵖ) :
      ∃ b : (R.over U).obj.obj X, s.val X = (n : (R.over U).obj.obj X) * b := by
    refine ⟨R.obj.map X.unop.hom.op a, ?_⟩
    change R.obj.map X.unop.hom.op f = _
    rw [ha, map_mul, map_natCast]
  have hi := localization_nsmul_iso (J.over U) (R.over U) n s hs
  let L := (DerivedCategory.singleFunctor (Mod (R.over U)) 0).obj
    (ringedSectionLocalization (R.over U) s)
  let := HasDerivedCategory.standard (Mod (R.over U))
  have hL : IsIso (n • 𝟙 L) := by
    have := hi
    rw [show n • 𝟙 L = (DerivedCategory.singleFunctor (Mod (R.over U)) 0).map
      (n • 𝟙 (ringedSectionLocalization (R.over U) s)) by
        rw [Functor.map_nsmul, Functor.map_id]]
    infer_instance
  exact hom_zero_of_orthogonal (J.over U) (R.over U) n _ L
    (restricted_orthogonal J R n M hM U) hL

end CategoryTheory.ConstantCompletion
