/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
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
public import Mathlib.CategoryTheory.Sites.Equivalence
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift
import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import all WeilConjectures.CategoryTheory.RingedSiteBoundedEvaluation.RingedSiteBoundedEvaluationAssembly

/-! # Internal Hom from a finite local system over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.13,
finite-coefficient local-system case; Stacks Project, Tag 0FNY, example-dual
(blueprint: lem-sfb-finite-field-lisse-internal-hom).

The two functors below spell out the two sides of the cohomology formula, including
all maps. The theorem asserts bounded constructibility in the original interval and
an isomorphism natural contravariantly in the local system and covariantly in the complex.
All derived categories are the ordinary, uncompleted localizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] CategoryTheory.RingedSiteBoundedEvaluation.smallColimits
  CategoryTheory.RingedSiteBoundedEvaluation.hasTotal
  CategoryTheory.RingedSiteBoundedEvaluation.finiteBiproducts

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
  (M P : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))

end PresheafOfModules

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
  {R : Sheaf J CommRingCat.{u + 1}}

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj R

section

variable {U : C}
end

variable {U : C} in
section
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

open CategoryTheory.RingedSiteBoundedEvaluation

end

end SheafOfModules

namespace AlgebraicGeometry.Scheme

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] WeilConjectures.sfAbBijective

/-- The bifunctor `(L,N) ↦ H^r RHom(L[0],N)` on the ordinary constant-ring module
category. The first variable is contravariant. Source: the K-injective construction
in Stacks, Cohomology on Sites, Section 08J7
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
def finiteFieldInternalHomCohomology (S : Scheme.{u}) (A : Type u) [Field A] (r : ℤ) :
    (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
      DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ⥤
        proEtaleRingModules S (proEtaleConstantRing S A) :=
  ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) 0).op.prod
    (𝟭 (DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))))) ⋙
    derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
      (ProEt.topology S) (proEtaleConstantRing S A) ⋙
    DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r

private def modelPresheafFunctor (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) where
  obj M := proEtaleConstantModulePresheafOfUniverses (Over U) A M
  map f := { app := fun _ ↦ f }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelPresheafFunctor S A U).Additive where
  map_add {X Y f g} := by ext; rfl

private def modelSheafFunctor (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      SheafOfModules.{u + 1}
        (((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)).over U) :=
  let : EssentiallySmall.{u + 1} (Over U) := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify ((ProEt.topology S).over U) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  let : ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses S A U).1
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses S A U).2
  modelPresheafFunctor S A U ⋙ _root_.PresheafOfModules.sheafification.{u + 1}
    (Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))

private instance sheafificationAdditive_ff
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat.{u + 1}} {R : Sheaf J RingCat.{u + 1}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] :
    (_root_.PresheafOfModules.sheafification.{u + 1} α).Additive := by
  let L := _root_.PresheafOfModules.sheafification.{u + 1} α
  have : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelSheafFunctor S A U).Additive := by
  dsimp only [modelSheafFunctor]
  infer_instance

private theorem fixedFiniteModels (S : Scheme.{u}) (A : Type u) [Field A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M) L) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((proEtaleModuleRestriction S A).obj L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := hL
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := he i
  let := hM
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a M
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj M :=
    E.mapIso eM ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a M)).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
  have : Finite M := Finite.of_equiv
    (Module.Free.ChooseBasisIndex B M → B) (Module.Free.chooseBasis B M).equivFun.toEquiv.symm
  exact ⟨M, inferInstance, ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

private def mapComplexBifunctor_ff
    {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    (F : B ⥤ C ⥤ D) [∀ b, (F.obj b).PreservesZeroMorphisms] :
    B ⥤ CochainComplex C ℤ ⥤ CochainComplex D ℤ where
  obj b := (F.obj b).mapHomologicalComplex (.up ℤ)
  map f := NatTrans.mapHomologicalComplex (F.map f) (.up ℤ)
  map_id b := by rw [F.map_id, NatTrans.mapHomologicalComplex_id]
  map_comp f g := by rw [F.map_comp, NatTrans.mapHomologicalComplex_comp]

private def HomComplexProjection_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ) :=
  ∀ (L M : CochainComplex C ℤ) (n p q : ℤ) (_h : p + n = q),
    (((G.obj (op L)).obj M).X n ⟶ (F.obj (op (L.X p))).obj (M.X q))

private def HomComplexLimit_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ L M n, IsLimit (Fan.mk (((G.obj (op L)).obj M).X n)
    (fun p ↦ π L M n p (p + n) rfl))

private def HomComplexDifferential_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
    ((G.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ (F.obj (op (L.X p))).map (M.d q' q) -
        n.negOnePow • (π L M n p' q hp' ≫ (F.map (L.d p p').op).app (M.X q))

private def HomComplexNaturality_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ {L L' M M'} (f : L' ⟶ L) (g : M ⟶ M') n p q (hpq : p + n = q),
    (((G.map f.op).app M) ≫ (G.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
      π L M n p q hpq ≫ (F.map (f.f p).op).app (M.X q) ≫
        (F.obj (op (L'.X p))).map (g.f q)

private def HomComplexZeroSource_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    : Prop :=
  ∀ X Y, IsZero X → IsZero ((F.obj (op X)).obj Y)

private lemma isIso_dependent_generic_ff
    {D : Type*} [Category D] {Z : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (Z ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

private def singleHomComplexGenericIso_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F) (L : C) (K : CochainComplex C ℤ) :
    (G.obj (op ((CochainComplex.singleFunctor C 0).obj L))).obj K ≅
      ((F.obj (op L)).mapHomologicalComplex (.up ℤ)).obj K := by
  classical
  let P := (CochainComplex.singleFunctor C 0).obj L
  let H := (G.obj (op P)).obj K
  let Q := fun n p : ℤ ↦ (F.obj (op (P.X p))).obj (K.X (p + n))
  let π := fun n p ↦ proj P K n p (p + n) rfl
  have hc (n : ℤ) : IsLimit (Fan.mk (H.X n) (π n)) := hlim P K n
  have hz (n p : ℤ) (h : p ≠ 0) : IsZero (Q n p) :=
    hzero _ _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 L p h)
  let v (n : ℤ) : Q n 0 ⟶ H.X n := Fan.IsLimit.lift (hc n)
    (fun p ↦ if h : p = 0 then eqToHom (congrArg (Q n) h.symm) else 0)
  have hv (n : ℤ) : v n ≫ π n 0 = 𝟙 (Q n 0) := by
    change Fan.IsLimit.lift (hc n) _ ≫ (Fan.mk (H.X n) (π n)).proj 0 = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ (n : ℤ) : π n 0 ≫ v n = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext (hc n)
    intro p
    change (π n 0 ≫ v n) ≫ π n p = 𝟙 (H.X n) ≫ π n p
    by_cases h : p = 0
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz n p h).eq_of_tgt _ _
  have hi (n : ℤ) : IsIso (proj P K n 0 n (Int.zero_add n)) := by
    have h := (Iso.mk (π n 0) (v n) (hπ n) (hv n)).isIso_hom
    exact isIso_dependent_generic_ff (fun q hq ↦ proj P K n 0 q hq) (Int.zero_add n) h
  let e (n : ℤ) : H.X n ≅ (F.obj (op L)).obj (K.X n) :=
    @asIso _ _ _ _ (proj P K n 0 n (Int.zero_add n)) (hi n)
  refine HomologicalComplex.Hom.isoOfComponents
    (C₁ := H) (C₂ := ((F.obj (op L)).mapHomologicalComplex (.up ℤ)).obj K) e ?_
  intro n m hnm
  have hm : m = n + 1 := hnm.symm
  subst m
  have hd := hdiff P K n (n + 1) 0 (n + 1)
    n 1 rfl (Int.zero_add _) (Int.zero_add _) (by omega)
  symm
  change H.d n (n + 1) ≫ proj P K (n + 1) 0 (n + 1) (Int.zero_add _) =
    proj P K n 0 n (Int.zero_add n) ≫ (F.obj (op L)).map (K.d n (n + 1))
  have hzero : (F.map (P.d 0 1).op).app (K.X (n + 1)) = 0 :=
    (hzero (P.X 1) _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 L 1 (by decide))).eq_of_src _ _
  rw [hzero, comp_zero, smul_zero, sub_zero] at hd
  exact hd

private lemma singleHomComplexGenericIso_hom_f_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F) (L : C) (K : CochainComplex C ℤ) (n : ℤ) :
    (singleHomComplexGenericIso_ff proj hlim hdiff hzero L K).hom.f n =
      proj ((CochainComplex.singleFunctor C 0).obj L) K n 0 n (Int.zero_add n) := rfl

attribute [local irreducible] singleHomComplexGenericIso_ff

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def singleHomComplexGenericNatIso_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F)
    (hnatural : HomComplexNaturality_ff C F G proj) :
    ((CochainComplex.singleFunctor C 0).op.prod (𝟭 _)) ⋙ Functor.uncurry.obj G ≅
      Functor.uncurry.obj (mapComplexBifunctor_ff F) := by
  refine NatIso.ofComponents
    (fun P ↦ singleHomComplexGenericIso_ff proj hlim hdiff hzero P.1.unop P.2) ?_
  intro P Q f
  ext n : 1
  simp only [HomologicalComplex.comp_f, singleHomComplexGenericIso_hom_f_ff]
  change (((G.map ((CochainComplex.singleFunctor C 0).map f.1.unop).op).app P.2) ≫
      (G.obj _).map f.2).f n ≫ proj _ _ n 0 n (Int.zero_add n) =
    proj _ _ n 0 n (Int.zero_add n) ≫
      (F.map f.1).app (P.2.X n) ≫ (F.obj Q.1).map (f.2.f n)
  rw [hnatural]
  have hs : ((CochainComplex.singleFunctor C 0).map f.1.unop).f 0 = f.1.unop := by
    change (𝟙 _ ≫ f.1.unop ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  erw [hs]
  rfl

namespace SiteHomComplex_ff
variable {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  {R : Sheaf J CommRingCat.{u + 1}}

set_option hygiene false in
local notation "𝓡" => (sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

private instance homAdditive (L : (SheafOfModules.{u + 1} 𝓡)ᵒᵖ) :
    ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L).Additive := by
  let F := (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L
  have : PreservesLimitsOfSize.{0, 0} F :=
    (SheafOfModules.tensorHomAdjunction_kfg R L.unop).rightAdjoint_preservesLimits
  exact Functor.additive_of_preserves_binary_products F

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem projectionNatural : HomComplexNaturality_ff
    (SheafOfModules.{u + 1} 𝓡)
    (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)
    (homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexπ.{u + 1, u, u + 1, u + 1} (R := R)) := by
  intro L L' M M' f g n p q h
  have h' := homComplexFunctor_map_f_π.{u + 1, u, u + 1, u + 1}
    (R := R) f g n p q h
  change _ = homComplexπ (R := R) _ _ n p q h ≫
    SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) ≫
      SheafOfModules.homObjMap (R := R) (𝟙 _) (g.f q)
  erw [SheafOfModules.homObjMap_comp_homObjMap]
  simp only [Category.id_comp]
  exact h'

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem homZeroSource : HomComplexZeroSource_ff
    (SheafOfModules.{u + 1} 𝓡)
    (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R) := by
  intro X Y hX
  apply (IsZero.iff_id_eq_zero _).mpr
  change 𝟙 (SheafOfModules.homObj (R := R) X Y) = 0
  rw [← SheafOfModules.homObjMap_id (R := R), hX.eq_of_src (𝟙 _) 0]
  exact (((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).flip.obj Y).map_zero
    (op X) (op X))

private def comparison :
    ((CochainComplex.singleFunctor (SheafOfModules.{u + 1} 𝓡) 0).op.prod (𝟭 _)) ⋙
      Functor.uncurry.obj (homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R)) ≅
        Functor.uncurry.obj (mapComplexBifunctor_ff
          (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)) := by
  let F := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R
  let : ∀ L, (F.obj L).PreservesZeroMorphisms := fun _ ↦ inferInstance
  exact singleHomComplexGenericNatIso_ff
    (F := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)
    (G := homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexπ.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexIsLimit.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplex_d_π.{u + 1, u, u + 1, u + 1} (R := R))
    (homZeroSource (R := R)) (projectionNatural (R := R))

end SiteHomComplex_ff

attribute [local irreducible] derivedInternalHomOfUniverses

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace SiteHomComplex_ff

variable {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

end SiteHomComplex_ff

attribute [local irreducible] DerivedCategory.homologyFunctor SheafOfModules.homFunctor

attribute [local semireducible] SheafOfModules.homFunctor
attribute [local irreducible] finiteFieldInternalHomCohomology

end AlgebraicGeometry.Scheme
