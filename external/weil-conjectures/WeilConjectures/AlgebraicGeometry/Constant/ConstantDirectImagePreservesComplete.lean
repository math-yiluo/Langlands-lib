/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
public import WeilConjectures.CategoryTheory.RingedSiteLocalization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.Constant.ConstantScalarDirectImageCompleteness
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal

/-! # Direct image preserves local derived completeness -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

private theorem complete_iff_constantElements
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (N : D (constant J A)) :
    IsComplete (quotient J A I 0) N ↔
      ∀ (a : A), a ∈ I → ∀ U : C,
        @IsRingedSiteCompleteElement C _ J (constant J A)
          (HasDerivedCategory.standard _) (fun _ ↦ HasDerivedCategory.standard _) N U
          ((constantSection (J := J) a).val (op U)) := by
  let : HasDerivedCategory (Mod (constant J A)) := HasDerivedCategory.standard _
  let : ∀ U : C, HasDerivedCategory (SheafOfModules.{u}
      ((siteModuleRings (constant J A)).over U)) := fun _ ↦ HasDerivedCategory.standard _
  have hker (U : C) : (kernelIdeal (quotient J A I 0)).sections U =
      Ideal.span (Set.range (fun a : I ↦
        (constantSection (J := J) (a : A)).val (op U))) := by
    dsimp only [kernelIdeal]
    rw [(kernelIdeal_existsUnique (quotient J A I 0)).exists.choose_spec U]
    have h := ((flat_and_quotients J A I).2.2 0 U).2
    convert h using 1
    apply congrArg Ideal.span
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, by simpa only [Nat.zero_add, pow_one] using a.property⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.val, by simpa only [Nat.zero_add, pow_one] using a.property⟩, rfl⟩
  constructor
  · intro h a ha U
    apply (localCompleteness_models_iff J (constant J A) N U _).mp
    apply h U _
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [hker]
    exact Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩
  · intro h U f ⟨y, hy⟩
    apply (localCompleteness_models_iff J (constant J A) N U f).mpr
    obtain ⟨S, hS, _, _, _⟩ := ringedSite_complete_elements_ideal J (constant J A) N
    apply (hS U f).mp
    have hle : (kernelIdeal (quotient J A I 0)).sections U ≤ S U := by
      rw [hker]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact (hS U _).mpr (h a.val a.property U)
    apply hle
    change y.val = f at hy
    exact hy ▸ y.property

/-- The derived geometric direct image preserves each local complete element.

Source: Stacks Project, algebraization.tex Tag 099J, lemma-pushforward-derived-complete;
Tag 0997, lemma-hom-from-Af; sites-cohomology.tex Tag 0A07
(blueprint: lem-sp-constant-direct-image-preserves-complete).

Proof: the sections formula for the constant quotient kernel identifies its ideal
on U with the ideal generated by the restrictions of constant a in I. The local
completeness model comparison and the complete-elements ideal theorem therefore
identify local I-completeness with completeness for every such constant a on every
slice. Apply constantScalarDirectImage_complete separately to each a in I, then
apply this criterion in reverse. The proof uses the whole generating set I, so no
choice of finite generators is needed here; I=0 and the zero ring are included. -/
theorem constantDirectImage_preservesComplete
    {C E : Type u} [SmallCategory C] [SmallCategory E]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology E)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u)}
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (F : InverseImageData L)
    (G : Mod (constant JD A) ⥤+ Mod (constant JC A))
    (aM : pull F (constantMap F A) ⊣ G.obj)
    [PreservesFiniteLimits (pull F (constantMap F A))]
    [PreservesFiniteColimits (pull F (constantMap F A))]
    (RF : D (constant JD A) ⥤ D (constant JC A))
    (ηG : G.obj.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q (constant JC A) ⟶
      Q (constant JD A) ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor ηG
      (HomologicalComplex.quasiIso (Mod (constant JD A)) (ComplexShape.up ℤ)))
    (hηG : ∀ J : Cx (constant JD A), J.IsKInjective → IsIso (ηG.app J)) :
    ∀ N : D (constant JD A), IsComplete (quotient JD A I 0) N →
      IsComplete (quotient JC A I 0) (RF.obj N) := by
  let : HasDerivedCategory (Mod (constant JD A)) := HasDerivedCategory.standard _
  let : ∀ U : E, HasDerivedCategory (SheafOfModules.{u}
      ((siteModuleRings (constant JD A)).over U)) := fun _ ↦ HasDerivedCategory.standard _
  intro N hN
  apply (complete_iff_constantElements JC A I (RF.obj N)).mpr
  intro a ha
  apply constantScalarDirectImage_complete JC JD A V adj F G aM RF ηG hRF hηG a N
  intro U
  apply (localCompleteness_models_iff JD (constant JD A) N U _).mp
  apply hN U _
  refine ⟨⟨(transportedConstantSection F A a).val (op U), ?_⟩, rfl⟩
  dsimp only [kernelIdeal]
  rw [(kernelIdeal_existsUnique (quotient JD A I 0)).exists.choose_spec U]
  exact transportedConstantSection_quotient F A I a ha (op U)

end CategoryTheory.ConstantCompletion
