/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
/-! # The principal image ideal and the covering-sieve local tests

Source: Stacks 0999, 099B and 03DA.
(blueprint: lem-pur-principal-ideal-local-test-criterion). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private theorem mono_range_local
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} (f : A ⟶ B) [Mono f]
    (U : C) (x : B.obj.obj (op U))
    (hx : Presheaf.imageSieve f.hom x ∈ J U) :
    ∃ y : A.obj.obj (op U), f.hom.app (op U) y = x := by
  have : Mono f.hom := inferInstanceAs (Mono ((sheafToPresheaf J (Type u)).map f))
  let G := Subfunctor.range f.hom
  have hG : Presieve.IsSheaf J G.toFunctor :=
    Presieve.isSheaf_iso J (asIso (Subfunctor.toRange f.hom))
      ((isSheaf_iff_isSheaf_of_type J A.obj).mp A.property)
  apply (Subfunctor.isSheaf_iff G
    ((isSheaf_iff_isSheaf_of_type J B.obj).mp B.property)).mp hG (op U) x
  exact hx

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "R" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
set_option hygiene false in
local notation "A" => SheafOfModules.{u} R

private theorem imageSection_iff
    (a : (SheafOfModules.unit R).sections) (U : C) (x : O.obj.obj (op U)) :
    (∃ y : (image (globalSectionMultiplication O a)).val.obj (op U),
      (image.ι (globalSectionMultiplication O a)).val.app (op U) y = x) ↔
      ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
        ∃ c : O.obj.obj (op V), O.obj.map f.op x =
          (show O.obj.obj (op V) from a.val (op V)) * c := by
  let μ := globalSectionMultiplication O a
  let π := factorThruImage μ
  let ι := image.ι μ
  let F : A ⥤ Sheaf J (Type u) :=
    SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat)
  have hmul (V : C) (c : O.obj.obj (op V)) :
      μ.val.app (op V) c = (show O.obj.obj (op V) from a.val (op V)) * c := by
    change c * (show O.obj.obj (op V) from a.val (op V)) = _
    exact mul_comm _ _
  let : (SheafOfModules.toSheaf.{u} R).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  constructor
  · rintro ⟨y, hy⟩
    have : Epi π := inferInstance
    have : Epi ((SheafOfModules.toSheaf.{u} R).map π) :=
      Functor.map_epi (SheafOfModules.toSheaf.{u} R) π
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{u} R).map π) :=
      (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{u} _).mpr inferInstance
    have : Sheaf.IsLocallySurjective (F.map π) :=
      inferInstanceAs (Sheaf.IsLocallySurjective
        ((sheafCompose J (forget AddCommGrpCat)).map
          ((SheafOfModules.toSheaf.{u} R).map π)))
    refine ⟨Presheaf.imageSieve (F.map π).hom y,
      Presheaf.imageSieve_mem J (F.map π).hom y, ?_⟩
    rintro V f ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hfac := congrArg (fun k ↦ k.val.app (op V) c) (image.fac μ)
    have hn := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map ι.val) f.op y
    change ι.val.app (op V) (π.val.app (op V) c) = μ.val.app (op V) c at hfac
    change π.val.app (op V) c = (image μ).val.map f.op y at hc
    rw [hc] at hfac
    rw [← hy]
    exact hn.symm.trans (hfac.trans (hmul V c))
  · rintro ⟨S, hS, hs⟩
    have : Mono ι := inferInstance
    have : Mono (F.map ι) := by
      have : Mono ι.val :=
        inferInstanceAs (Mono ((SheafOfModules.forget R).map ι))
      apply (sheafToPresheaf J (Type u)).mono_of_mono_map
      let (X : Cᵒᵖ) : Mono (((sheafToPresheaf J (Type u)).map (F.map ι)).app X) :=
        ConcreteCategory.mono_of_injective _
          (PresheafOfModules.injective_of_mono ι.val X)
      exact NatTrans.mono_of_mono_app _
    apply mono_range_local (F.map ι) U x
    refine J.superset_covering ?_ hS
    intro V f hf
    obtain ⟨c, hc⟩ := hs V f hf
    refine ⟨π.val.app (op V) c, ?_⟩
    have hfac := congrArg (fun k ↦ k.val.app (op V) c) (image.fac μ)
    exact hfac.trans ((hmul V c).trans hc.symm)

private theorem sliceSection_eq (U : C)
    (s : ((O.over U).obj ⋙ forget CommRingCat).sections) :
    s = ringedSliceSection O U (s.val (op (Over.mk (𝟙 U)))) := by
  ext X
  have h := s.property (show op (Over.mk (𝟙 U)) ⟶ X from
    (Over.homMk X.unop.hom (by simp)).op)
  exact h.symm

variable [HasDerivedCategory.{w} A]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} ((R).over U))]


/-- The principal image ideal gives exactly the covering-sieve formulation of local completeness. An
image section locally lifts along the epimorphism onto the image and therefore is locally a
scalar multiple. Conversely local scalar multiples locally lie in the image subsheaf, and the
sheaf property of this subobject descends them to an image section. A compatible slice section
is determined by its terminal value; substitute this value in both formulations. Their
localization and exact derived-restriction tests then agree. This includes the zero and unit
ideals.

Source: Stacks 0999, 099B and 03DA.
(blueprint: lem-pur-principal-ideal-local-test-criterion). -/
theorem principalLocallyComplete_iff
    (a : (O.obj ⋙ forget CommRingCat).sections) (N : DerivedCategory A) :
    letI : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))) :=
        principalLocalTestSliceDerived O
    principalLocallyComplete.{u, u, u, w} O a N ↔
      IsLocallyDerivedRingedIdealComplete.{u, w} O (image (ringedKoszulScalar O a).asHom)
        (image.ι (ringedKoszulScalar O a).asHom) N := by
  let : ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
    ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))) :=
      principalLocalTestSliceDerived O
  constructor
  · intro h U f hf
    let a' : (SheafOfModules.unit R).sections := ⟨a.val, a.property⟩
    obtain ⟨S, hS, hs⟩ := (imageSection_iff O a' U f).mp hf
    have hh := h U (ringedSliceSection O U f) ⟨S, hS, by
      intro V g hg
      exact hs V g hg⟩
    exact hh
  · intro h U s hs
    rw [sliceSection_eq O U s] at *
    let a' : (SheafOfModules.unit R).sections := ⟨a.val, a.property⟩
    have hi := (imageSection_iff O a' U (s.val (op (Over.mk (𝟙 U))))).mpr hs
    exact h U _ hi

end CategoryTheory
