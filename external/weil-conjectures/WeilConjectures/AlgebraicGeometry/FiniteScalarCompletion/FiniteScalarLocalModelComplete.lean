/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import all WeilConjectures.Algebra.Homology.RoosSplitComparison
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import WeilConjectures.CategoryTheory.Finite.FinitePowerComplex
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.IntegralCoefficientQuotientLimit
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarLocalModelRepresentatives
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralModelSurjectiveClosedReflection
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.CondensedCoverRestrictionConservative
public import Mathlib.RingTheory.DedekindDomain.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-! # Completeness of finite constant scalar local models

Source: blueprint main-20261015, localizing-closure-ctf-equals-bc, Local models and
Locality; Bhatt--Scholze, Sections 3.1 and 3.4
(blueprint: lem-sfb-finite-scalar-local-model-complete).

The ambient category is the ordinary unbounded derived category of internal modules
on the small pro-etale site. Natural-number level n denotes the exponent n+1.
Finite powers, quotient maps and the quotient tower below use the actual coefficient
maps of `AdicCompletion`. No choice of unrelated levelwise isomorphisms is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CochainComplex
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteScalarCompletion

open AlgebraicGeometry.ProEtale.AdicCompletion
open AlgebraicGeometry.ProEtale.PrincipalReduction

attribute [local instance 1100] HasFiniteBiproducts.out

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private local instance moduleSmallLimits : HasLimitsOfSize.{0, 0} (Modules l E T) :=
  hasLimitsOfSizeShrink (Modules l E T)

private local instance complexSmallLimits :
    HasLimitsOfSize.{0, 0} (CochainComplex (Modules l E T) ℤ) :=
  ⟨fun _ _ ↦ HomologicalComplex.instHasLimitsOfShape⟩

private local instance complexCountableProducts :
    HasCountableProducts (CochainComplex (Modules l E T) ℤ) :=
  ⟨fun _ _ ↦ HomologicalComplex.instHasLimitsOfShape⟩

/-- Use the degreewise product directly, avoiding countable-index shrinking.
Source: categorical limits of homological complexes
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
local instance (priority := 1100) complexProduct
    {A : Type*} [Category A] [HasZeroMorphisms A]
    [HasLimitsOfShape (Discrete ℕ) A] (H : ℕ → CochainComplex A ℤ) : HasProduct H :=
  (HomologicalComplex.instHasLimitsOfShape (C := A) (J := Discrete ℕ)
    (c := .up ℤ)).has_limit (Discrete.functor H)

/-- The finite free coefficient module, placed in degree zero, including rank zero.
Source: blueprint Local models, finite free case
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def freeComplex (d : ℕ) : CochainComplex (Modules l E T) ℤ :=
  (singleFunctor (Modules l E T) 0).obj (Mod.finiteFree (ring l E T) d)

/-- The finite power of the actual positive quotient, with its integral scalar action.
Source: blueprint Local models, quotient tower
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
abbrev quotientPower (d n : ℕ) : Modules l E T :=
  ⨁ fun _ : Fin d ↦ finiteModule l E T n

/-- Coordinatewise scalar reduction from the free coefficient module.
Source: blueprint Local models, specified scalar quotient projections
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def powerQuotient (d n : ℕ) :
    Mod.finiteFree (ring l E T) d ⟶ quotientPower l E T d n :=
  biproduct.map fun _ : Fin d ↦ finiteUnit l E T n

/-- The actual coordinatewise quotient transition from exponent n+2 to n+1.
Source: blueprint Local models, quotient tower
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def powerStep (d n : ℕ) :
    quotientPower l E T d (n + 1) ⟶ quotientPower l E T d n :=
  biproduct.map fun _ : Fin d ↦
    (DerivedNakayama.pullback l E T).map (quotientStep l E n)

/-- Finite biproduct power, retaining the specified coordinate maps.
Source: blueprint Local models, finite free case
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def finiteBiproductPower {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] (d : ℕ) : A ⥤ A where
  obj M := ⨁ fun _ : Fin d ↦ M
  map f := biproduct.map fun _ : Fin d ↦ f
  map_id M := by ext i; simp
  map_comp f g := by ext i; simp

/-- The actual quotient sequence as a functor to degree-zero complexes.
Source: blueprint Local models, free tower comparison
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def quotientSequence (d : ℕ) : ℕᵒᵖ ⥤ CochainComplex (Modules l E T) ℤ :=
  coefficientSequence l E T ⋙ finiteBiproductPower d ⋙ singleFunctor (Modules l E T) 0

/-- Assemble a diagram of cochain complexes as a complex of diagrams.
Source: categorical interchange of functor and complex structures
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def complexOfSequence {A J : Type*} [Category A] [Category J]
    [HasZeroMorphisms A] (F : J ⥤ CochainComplex A ℤ) :
    CochainComplex (J ⥤ A) ℤ where
  X k := F ⋙ HomologicalComplex.eval A (.up ℤ) k
  d k r := { app := fun j ↦ (F.obj j).d k r
             naturality := fun _ _ f ↦ (F.map f).comm k r }
  shape k r h := NatTrans.ext (funext fun j ↦ (F.obj j).shape k r h)
  d_comp_d' k r t _ _ := NatTrans.ext (funext fun j ↦ (F.obj j).d_comp_d k r t)

/-- The strict quotient tower in degree zero, using the actual quotient transitions.
Source: blueprint Local models, free tower comparison
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def quotientTower (d : ℕ) : CochainComplex (ℕᵒᵖ ⥤ Modules l E T) ℤ :=
  complexOfSequence (quotientSequence l E T d)

/-- Scalar reduction as a chain map to a level of the strict quotient tower.
Source: blueprint Local models, specified scalar quotient projections
(blueprint: lem-sfb-finite-scalar-local-model-complete). -/
def quotientChainMap (d n : ℕ) :
    freeComplex l E T d ⟶ (quotientTower l E T d).asFunctor.obj (op n) :=
  (singleFunctor (Modules l E T) 0).map (powerQuotient l E T d n)

private local instance cachedFiniteBiproducts : HasFiniteBiproducts (Modules l E T) :=
  inferInstance

private local instance cachedAbelian : Abelian (Modules l E T) := inferInstance

private local instance cachedComplexAbelian :
    Abelian (CochainComplex (Modules l E T) ℤ) := inferInstance

private theorem forall_int_next {P : ℤ → Prop} (h : ∀ p, P (p + 1)) (k : ℤ) : P k :=
  (congrArg P (show k - 1 + 1 = k by omega)).mp (h (k - 1))

set_option backward.isDefEq.respectTransparency false in
private theorem roosLift_quasiIso
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {C : CochainComplex A ℤ} (i : C ⟶ roosP N) (hi : i ≫ roosU N = 0)
    (hker : IsLimit (KernelFork.ofι i hi))
    (hepi : ∀ p : ℤ, Epi ((roosU N).f p)) : QuasiIso (roosLift i hi) := by
  let e : C ≅ kernel (roosU N) := hker.conePointUniqueUpToIso (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (roosU N) = i :=
    hker.conePointUniqueUpToIso_hom_comp (limit.isLimit _) WalkingParallelPair.zero
  have hκ : QuasiIso (CochainComplex.comparison (roosU N)) :=
    CochainComplex.comparison_quasiIso (roosU N) hepi
  have h : roosLift i hi = e.hom ≫ CochainComplex.comparison (roosU N) := by
    apply HomologicalComplex.Hom.ext
    funext k
    suffices ∀ p : ℤ, (roosLift i hi).f (p + 1) =
        (e.hom ≫ CochainComplex.comparison (roosU N)).f (p + 1) from forall_int_next
      (P := fun r ↦ (roosLift i hi).f r =
        (e.hom ≫ CochainComplex.comparison (roosU N)).f r) this k
    intro p
    apply (cancel_mono (roosχ N p).hom).mp
    rw [roosLift_χ]
    simp only [HomologicalComplex.comp_f, roosχ, Iso.trans_hom, Category.assoc]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.braiding_hom,
        biprod.lift_fst, cofiber_biprod_snd]
      rw [(CochainComplex.comparison_projections (roosU N) (p + 1) p
        (by omega)).1, comp_zero]
    · simp only [Category.assoc, biprod.lift_snd, biprod.braiding_hom,
        biprod.lift_snd, cofiber_biprod_fst]
      rw [(CochainComplex.comparison_projections (roosU N) (p + 1) p
        (by omega)).2]
      exact (congrArg (fun f ↦ f.f (p + 1)) he).symm
  rw [h]
  exact quasiIso_comp _ _

set_option backward.isDefEq.respectTransparency false in
private theorem roosU_degreewise_epi
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] (hrep : EpiπAppZeroOfEpi A)
    {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (hN : ∀ (p : ℤ) (n : ℕ), Epi ((N.X p).map (homOfLE n.le_succ).op))
    (p : ℤ) : Epi ((roosU N).f p) := by
  let P : Fan (fun n : ℕ ↦ (N.X p).obj (op n)) :=
    Fan.mk ((roosP N).X p) (RoosConeCalculus.π N p)
  have hP : IsLimit P := RoosConeCalculus.productLimit N p
  let t : P.pt ⟶ P.pt := 𝟙 _ - (roosU N).f p
  have ht (n : ℕ) : t ≫ P.proj n =
      P.proj (n + 1) ≫ (N.X p).map (homOfLE n.le_succ).op := by
    change (𝟙 _ - (roosU N).f p) ≫ RoosConeCalculus.π N p n = _
    erw [Preadditive.sub_comp, Category.id_comp, RoosConeCalculus.π_u]
    exact sub_sub_cancel _ _
  have h := epi_one_sub_of_epiπAppZeroOfEpi
    hrep (hN p) hP t ht
  change Epi (𝟙 ((roosP N).X p) -
    (𝟙 ((roosP N).X p) - (roosU N).f p)) at h
  rw [sub_sub_cancel] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem roosAugment_quasiIso
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (c : Cone N.asFunctor) (hc : IsLimit c)
    (f : ∀ n : ℕ, c.pt ⟶ N.asFunctor.obj (op n))
    (hf : ∀ n : ℕ, f (n + 1) ≫ N.asFunctor.map (homOfLE n.le_succ).op = f n)
    (hleg : ∀ n : ℕ, f n = c.π.app (op n))
    (hepi : ∀ p : ℤ, Epi ((roosU N).f p)) : QuasiIso (roosAugment f hf) := by
  let i := Pi.lift f
  obtain ⟨hz, ⟨hk⟩⟩ := CategoryTheory.roos_kernel N.asFunctor c hc
    (Fan.mk _ (fun n ↦ Pi.π _ n)) (productIsProduct _) i (roosU N)
    (fun n ↦ (Pi.lift_comp_π f n).trans (hleg n)) (by
      intro n
      exact (towerTransitionEndomorphism_eq_iff _ _).mp rfl n)
  exact roosLift_quasiIso i hz hk hepi

attribute [local irreducible] roosF

private theorem single_shortExact
    {A : Type*} [Category A] [Abelian A]
    (S : ShortComplex A) (hs : S.ShortExact) :
    (S.map (singleFunctor A 0)).ShortExact := by
  have : PreservesFiniteLimits (singleFunctor A 0) :=
    HomologicalComplex.instPreservesFiniteLimitsSingle (C := A) (c := .up ℤ) 0
  have : PreservesFiniteColimits (singleFunctor A 0) :=
    HomologicalComplex.instPreservesFiniteColimitsSingle (C := A) (c := .up ℤ) 0
  exact hs.map_of_exact (singleFunctor A 0)

private theorem complete_iso
    {K L : DerivedCategory (Modules l E T)} (e : K ≅ L)
    (hK : IsDerivedComplete l E T K) : IsDerivedComplete l E T L := by
  obtain ⟨P, hP, ⟨i⟩, hc⟩ := hK
  exact ⟨P, hP, ⟨i ≪≫ e⟩, hc⟩

attribute [local irreducible] IsDerivedComplete

section
attribute [local irreducible] freeComplex

private theorem complete_shortExact
    (S : ShortComplex (Modules l E T)) (hS : S.ShortExact)
    (h₁ : IsDerivedComplete l E T
      (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj S.X₁)))
    (h₂ : IsDerivedComplete l E T
      (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj S.X₂))) :
    IsDerivedComplete l E T
      (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj S.X₃)) := by
  obtain ⟨data, hdata, a, F, c, κ, sF, hadd, ha, hc, hrep, hcomplete, hshift, htri⟩ :=
    CompletionTriangle.completion_triangle_comparison l E T
  let D := hS.singleTriangle
  have hD := hS.singleTriangle_distinguished
  obtain ⟨hFD, γ, hγ₁, hγ₂, hγ₃⟩ := htri D hD
  have h₁' : IsDerivedComplete l E T D.obj₁ :=
    complete_iso l E T ((DerivedCategory.singleFunctorIsoCompQ _ 0).app S.X₁).symm h₁
  have h₂' : IsDerivedComplete l E T D.obj₂ :=
    complete_iso l E T ((DerivedCategory.singleFunctorIsoCompQ _ 0).app S.X₂).symm h₂
  have h₃ : IsDerivedComplete l E T D.obj₃ := by
    apply (hcomplete _).mpr
    rw [← hγ₃]
    apply CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ γ hD hFD
    · rw [hγ₁]
      exact (hcomplete _).mp h₁'
    · rw [hγ₂]
      exact (hcomplete _).mp h₂'
  exact complete_iso l E T ((DerivedCategory.singleFunctorIsoCompQ _ 0).app S.X₃) h₃

end

private theorem ordinary_scalar_complete
    (hfree : ∀ d : ℕ,
      IsDerivedComplete l E T (DerivedCategory.Q.obj (freeComplex l E T d)))
    (P : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    [Module.FinitePresentation (Padic.coefficientExtensionIntegers l E) P] :
    IsDerivedComplete l E T (DerivedCategory.Q.obj
      ((singleFunctor (Modules l E T) 0).obj
        ((FiniteConstantModel.integralModel l E T).obj P))) := by
  obtain ⟨a, b, f, g, ha, hf, hex, hg, ⟨ea⟩, ⟨eb⟩, ht, w, hs, rest⟩ :=
    (FiniteConstantModel.finite_constant_model_two_term_free_resolution l E T).1 P
  apply complete_shortExact l E T (ShortComplex.mk _ _ w) hs
  · exact complete_iso l E T
      (DerivedCategory.Q.mapIso ((singleFunctor (Modules l E T) 0).mapIso ea.symm))
      (by simpa only [freeComplex] using hfree a)
  · exact complete_iso l E T
      (DerivedCategory.Q.mapIso ((singleFunctor (Modules l E T) 0).mapIso eb.symm))
      (by simpa only [freeComplex] using hfree b)

private def ringLocalPredicate (A : Type u) [CommRing A]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R]
    [IsCommMonObj R]
    (models : ∀ (U : Scheme.{u}) (m n : ℕ), Matrix (Fin n) (Fin m) A →
      Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj R U))
    (X : Scheme.{u}) : Prop :=
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X),
    HasFiniteConstantLocalModel R X M ↔
      ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
        ∃ (m n : ℕ) (q : Matrix (Fin n) (Fin m) A),
          Nonempty ((CondensedRing.upperStar R (𝒰.f i)).obj M ≅ models (𝒰.X i) m n q)

private theorem source_representatives :
    ringLocalPredicate (Padic.coefficientExtensionIntegers l E)
      (integralModelCondensedCoefficients l E).X
      (sfbIntegralScalarPresentationModel l E) T := by
  unfold ringLocalPredicate
  intro M
  exact (proetale_scalar_local_model_representatives l E T).2 M

private def scalarLocalPredicate (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (X : Scheme.{u}) : Prop :=
  ringLocalPredicate A (Profinite.continuousCoefficientRingObj A)
    (fun U m n q ↦ (FiniteConstantModel.modelFunctor A U).obj
      (sfbScalarPresentationModule A m n q)) X

private theorem spectral_representatives :
    letI := spectralNorm.normedField (Padic l) E
    scalarLocalPredicate (Padic.coefficientExtensionIntegers l E) T := by
  let := spectralNorm.normedField (Padic l) E
  have hmodels : sfbIntegralScalarPresentationModel l E =
      (fun U m n q ↦ (FiniteConstantModel.modelFunctor
        (Padic.coefficientExtensionIntegers l E) U).obj
          (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) := rfl
  have h := source_representatives l E T
  rw [hmodels] at h
  exact h

private theorem topology_transport {A : Type*} [CommRing A]
    (P : ∀ t : TopologicalSpace A, @IsTopologicalRing A t _ → Prop)
    (t₁ t₂ : TopologicalSpace A) (ht : t₁ = t₂)
    (r₁ : @IsTopologicalRing A t₁ _) (r₂ : @IsTopologicalRing A t₂ _) :
    P t₁ r₁ → P t₂ r₂ := by
  subst t₂
  exact id

private def absoluteLocalPredicate : Prop :=
  ringLocalPredicate (Padic.coefficientExtensionIntegers l E) (DerivedNakayama.integerRing l E)
    (fun U m n q ↦ (FiniteConstantModel.integralModel l E U).obj
      (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) T

private theorem absolute_transport
    (h : letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      scalarLocalPredicate (Padic.coefficientExtensionIntegers l E) T) :
    absoluteLocalPredicate l E T := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hmodels : (fun U m n q ↦ (FiniteConstantModel.integralModel l E U).obj
      (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) =
      (fun U m n q ↦ (FiniteConstantModel.modelFunctor
        (Padic.coefficientExtensionIntegers l E) U).obj
          (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) := rfl
  unfold absoluteLocalPredicate
  rw [hmodels]
  exact h

private theorem absolute_representatives (h : absoluteLocalPredicate l E T) : ∀ M : Modules l E T,
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M ↔
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : 𝒰.I₀,
          ∃ (m n : ℕ)
            (q : Matrix (Fin n) (Fin m) (Padic.coefficientExtensionIntegers l E)),
            Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (𝒰.f i)).obj M ≅ (FiniteConstantModel.integralModel l E (𝒰.X i)).obj
                (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) := by
  unfold absoluteLocalPredicate ringLocalPredicate at h
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem local_model_representatives : ∀ M : Modules l E T,
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M ↔
        ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage T, ∀ i : 𝒰.I₀,
          ∃ (m n : ℕ)
            (q : Matrix (Fin n) (Fin m) (Padic.coefficientExtensionIntegers l E)),
            Nonempty ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (𝒰.f i)).obj M ≅ (FiniteConstantModel.integralModel l E (𝒰.X i)).obj
                (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)) := by
  let A := Padic.coefficientExtensionIntegers l E
  let t₁ : TopologicalSpace A := TopologicalSpace.induced
    (fun x : A ↦ (x : E))
    (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
  let t₂ : TopologicalSpace A := TopologicalSpace.induced
    (fun x : A ↦ (x : E))
    (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace.toTopologicalSpace
  have r₁ : @IsTopologicalRing A t₁ _ := by
    let := spectralNorm.normedField (Padic l) E
    infer_instance
  have r₂ : @IsTopologicalRing A t₂ _ := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    infer_instance
  have hti := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced (fun x : A ↦ (x : E)) t)
    (DerivedNakayama.coefficientTopology l E)
  have hsource : @scalarLocalPredicate _ _ t₁ r₁ T := by
    exact spectral_representatives l E T
  have htarget : @scalarLocalPredicate _ _ t₂ r₂ T :=
    topology_transport (fun t r ↦ @scalarLocalPredicate _ _ t r T)
      t₁ t₂ hti r₁ r₂ hsource
  exact absolute_representatives l E T (absolute_transport l E T htarget)

private def mapDerivedSingleIso
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : A) (N : B) (e : F.obj M ≅ N) :
    F.mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((singleFunctor A 0).obj M)) ≅
      DerivedCategory.Q.obj ((singleFunctor B 0).obj N) :=
  F.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app M) ≪≫
      DerivedCategory.Q.mapIso ((singleFunctor B 0).mapIso e)

section
attribute [local irreducible] freeComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_complete_of_free
    (hfree : ∀ (X : Scheme.{u}) (d : ℕ),
      IsDerivedComplete l E X (DerivedCategory.Q.obj (freeComplex l E X d)))
    (M : Modules l E T)
    (hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M) :
    IsDerivedComplete l E T
      (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj M)) := by
  classical
  obtain ⟨S, hS, hlocal, hsection, hrestrict⟩ :=
    StrictCompletionRestriction.strict_completion_restriction_comparison (l := l) (E := E)
  have hcomplete (X : Scheme.{u}) (K : DerivedCategory (Modules l E X)) :
      IsDerivedComplete l E X K ↔ IsIso ((S X).unit.app K) := by
    obtain ⟨data, hd, ht, hs, hr, hu, hc⟩ := hS X
    exact CompletionTriangle.complete_iff_from_comparison l E X
      (S X).completion (S X).unit hc K
  obtain ⟨𝒰, h𝒰⟩ := (local_model_representatives l E T M).mp hM
  apply (hcomplete T _).mpr
  apply ((condensed_cover_restriction_conservative
    (Mon.mk (DerivedNakayama.integerRing l E)) T 𝒰).1 _ _ _).mpr
  intro i
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) (𝒰.f i)
  have hweak : WeaklyEtale (𝒰.f i) :=
    (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale T 𝒰.mem₀) ⟨i⟩
  have hmem : (MorphismProperty.multiplicativeClosure
      (fun {V W : Scheme.{u}} (f : V ⟶ W) ↦ IsImmersion f ∨ WeaklyEtale f)) (𝒰.f i) :=
    MorphismProperty.le_multiplicativeClosure _ _ (Or.inr hweak)
  obtain ⟨hprod, ⟨c⟩⟩ := hrestrict (𝒰.f i) hmem
  obtain ⟨m, n, q, ⟨e⟩⟩ := h𝒰 i
  let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.1
  have : Module.Finite (Padic.coefficientExtensionIntegers l E)
      (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q) := by
    dsimp only [sfbScalarPresentationModule, ModuleCat.carrier]
    infer_instance
  have : Module.FinitePresentation (Padic.coefficientExtensionIntegers l E)
      (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q) := by
    exact Module.finitePresentation_of_finite _ _
  have hc := ordinary_scalar_complete l E (𝒰.X i) (hfree (𝒰.X i))
    (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q)
  let C := (singleFunctor (Modules l E T) 0).obj M
  have eF : F.obj M ≅
      (FiniteConstantModel.integralModel l E (𝒰.X i)).obj
        (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q) := e
  let ei : F.mapDerivedCategory.obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj ((singleFunctor (Modules l E (𝒰.X i)) 0).obj
        ((FiniteConstantModel.integralModel l E (𝒰.X i)).obj
          (sfbScalarPresentationModule (Padic.coefficientExtensionIntegers l E) m n q))) :=
    mapDerivedSingleIso F M _ eF
  have hi : IsIso ((S (𝒰.X i)).unit.app
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj C))) :=
    (hcomplete _ _).mp (complete_iso l E (𝒰.X i) ei.symm hc)
  have hcomp : IsIso (F.mapDerivedCategory.map ((S T).unit.app
      (DerivedCategory.Q.obj C)) ≫ c.derived.hom.app (DerivedCategory.Q.obj C)) := by
    rw [c.unit]
    exact hi
  exact IsIso.of_isIso_comp_right _ (c.derived.hom.app (DerivedCategory.Q.obj C))

end

private theorem point_complete_of_local
    (hloc : ∀ M : Modules l E T,
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M →
      IsDerivedComplete l E T
        (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj M)))
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (DerivedNakayama.integerRing l E))
    (hP : Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P) :
    IsDerivedComplete l E T (DerivedCategory.Q.obj
      ((singleFunctor (Modules l E T) 0).obj ((DerivedNakayama.pullback l E T).obj P))) := by
  apply hloc
  refine ⟨.singleton (𝟙 T) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩
  exact ⟨P, hP, pointModelPullback (𝟙 T) _ P⟩

private def bipowerIso {A : Type*} [Category A] [Abelian A] [HasFiniteBiproducts A] (d : ℕ) :
    finiteBiproductPower (A := A) d ≅ finitePowerFunctor d :=
  NatIso.ofComponents (fun M ↦ biproduct.isoProduct (fun _ : Fin d ↦ M)) (by
    intro M N f
    apply Pi.hom_ext
    intro i
    simp [finiteBiproductPower, finitePowerFunctor, biproduct.isoProduct_hom])

private instance bipowerLimits {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] (d : ℕ) :
    PreservesFiniteLimits (finiteBiproductPower (A := A) d) := by
  have : PreservesFiniteLimits (finitePowerFunctor (A := A) d) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_natIso (bipowerIso d).symm

private instance bipowerAllLimits {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] (d : ℕ) {J : Type*} [Category J] [HasLimitsOfShape J A] :
    PreservesLimitsOfShape J (finiteBiproductPower (A := A) d) :=
  preservesLimitsOfShape_of_natIso (bipowerIso d).symm

private instance bipowerColimits {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] (d : ℕ) :
    PreservesFiniteColimits (finiteBiproductPower (A := A) d) :=
  preservesFiniteColimits_of_natIso (bipowerIso d).symm

private def powerScalar (d n : ℕ) :
    Mod.finiteFree (ring l E T) d ⟶ Mod.finiteFree (ring l E T) d :=
  biproduct.map fun _ : Fin d ↦
    DerivedNakayama.unitEndOnX l E T (DerivedNakayama.uniformizerEnd l E ^ (n + 1)) •
      𝟙 (𝟙_ (Modules l E T))

private theorem power_ses (d n : ℕ) :
    ∃ w : powerScalar l E T d n ≫ powerQuotient l E T d n = 0,
      (ShortComplex.mk (powerScalar l E T d n) (powerQuotient l E T d n) w).ShortExact := by
  obtain ⟨w, hw⟩ := CoefficientCone.coefficient_ses l E T n
  exact ⟨_, hw.map_of_exact (finiteBiproductPower d)⟩

attribute [local irreducible] powerScalar

private theorem bipower_smul {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] {R : Type*} [Semiring R] [Linear R A]
    (M N : A) (f : M ⟶ N) (r : R) (d : ℕ) :
    (biproduct.map fun _ : Fin d ↦ r • f) =
      r • (biproduct.map fun _ : Fin d ↦ f) := by
  apply biproduct.hom_ext
  intro i
  simp

private theorem single_smul {A : Type*} [Category A] [Abelian A]
    {R : Type*} [Semiring R] [Linear R A] {M N : A} (r : R) (f : M ⟶ N) :
    (singleFunctor A 0).map (r • f) = r • (singleFunctor A 0).map f := by
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  apply HomologicalComplex.from_single_hom_ext
  change ((HomologicalComplex.single A (.up ℤ) 0).map (r • f)).f 0 =
    r • ((HomologicalComplex.single A (.up ℤ) 0).map f).f 0
  rw [HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp

private theorem single_bipower_smul {A : Type*} [Category A] [Abelian A]
    [HasFiniteBiproducts A] {R : Type*} [Semiring R] [Linear R A]
    (M : A) (r : R) (d : ℕ) :
    r • 𝟙 ((singleFunctor A 0).obj (⨁ fun _ : Fin d ↦ M)) =
      (singleFunctor A 0).map (biproduct.map fun _ : Fin d ↦ r • 𝟙 M) := by
  rw [bipower_smul, single_smul]
  have h : (biproduct.map fun _ : Fin d ↦ 𝟙 M) = 𝟙 _ := by
    apply biproduct.hom_ext
    intro i
    simp
  rw [h, CategoryTheory.Functor.map_id]

private theorem scalar_free (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T) (d n : ℕ) :
    scalar l E T data.d n (freeComplex l E T d) =
      (singleFunctor (Modules l E T) 0).map (powerScalar l E T d n) := by
  unfold scalar freeComplex
  rw [CoefficientCone.scalar_eq l E T data hdata, DerivedNakayama.scalarOnComplex_eq]
  unfold powerScalar
  exact single_bipower_smul (𝟙_ (Modules l E T))
    (DerivedNakayama.unitEndOnX l E T (DerivedNakayama.uniformizerEnd l E ^ (n + 1))) d

attribute [local irreducible] DerivedNakayama.scalarOnComplex

private theorem shortExact_congr_first
    {A : Type*} [Category A] [Abelian A] {X Y Z : A}
    {f f' : X ⟶ Y} {g : Y ⟶ Z} (h : f = f')
    (w : f' ≫ g = 0) (hs : (ShortComplex.mk f' g w).ShortExact) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact := by
  subst f'
  exact ⟨w, hs⟩

private theorem chain_ses (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T) (d n : ℕ) :
    ∃ w : scalar l E T data.d n (freeComplex l E T d) ≫
        quotientChainMap l E T d n = 0,
      (ShortComplex.mk (scalar l E T data.d n (freeComplex l E T d))
        (quotientChainMap l E T d n) w).ShortExact := by
  obtain ⟨w, hw⟩ := power_ses l E T d n
  exact shortExact_congr_first (scalar_free l E T data hdata d n) _
    (single_shortExact (ShortComplex.mk _ _ w) hw)

private def quotientLevel (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T) (d n : ℕ) :
    (data.D n).obj (freeComplex l E T d) ⟶
      (quotientTower l E T d).asFunctor.obj (op n) :=
  (eqToIso (data.hobj n (freeComplex l E T d))).hom ≫
    mappingCone.descShortComplex
      (ShortComplex.mk (scalar l E T data.d n (freeComplex l E T d))
        (quotientChainMap l E T d n)
        (chain_ses l E T data hdata d n).choose)

private theorem quotientLevel_quasiIso (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T) (d n : ℕ) :
    QuasiIso (quotientLevel l E T data hdata d n) := by
  let S := ShortComplex.mk (scalar l E T data.d n (freeComplex l E T d))
        (quotientChainMap l E T d n)
    (chain_ses l E T data hdata d n).choose
  have hS : S.ShortExact := (chain_ses l E T data hdata d n).choose_spec
  have : QuasiIso (mappingCone.descShortComplex S) :=
    mappingCone.quasiIso_descShortComplex (S := S) hS
  change QuasiIso ((eqToIso (data.hobj n (freeComplex l E T d))).hom ≫
    mappingCone.descShortComplex S)
  exact quasiIso_comp _ _

private theorem powerQuotient_step (d n : ℕ) :
    powerQuotient l E T d (n + 1) ≫ powerStep l E T d n =
      powerQuotient l E T d n := by
  unfold powerQuotient powerStep
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  rw [AdicCompletion.finiteUnit_step]

private theorem quotientSequence_step (d n : ℕ) :
    (quotientSequence l E T d).map (homOfLE n.le_succ).op =
      (singleFunctor (Modules l E T) 0).map (powerStep l E T d n) := by
  dsimp only [quotientSequence, Functor.comp_map, coefficientSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientChainMap_step (d n : ℕ) :
    quotientChainMap l E T d (n + 1) ≫
      (quotientTower l E T d).asFunctor.map (homOfLE n.le_succ).op =
        quotientChainMap l E T d n := by
  apply HomologicalComplex.Hom.ext
  funext p
  have hs := congrArg (fun f ↦ f.f p) (quotientSequence_step l E T d n)
  change ((singleFunctor (Modules l E T) 0).map
    (powerQuotient l E T d (n + 1))).f p ≫
      ((quotientSequence l E T d).map (homOfLE n.le_succ).op).f p = _
  rw [hs, ← HomologicalComplex.comp_f, ← Functor.map_comp, powerQuotient_step]
  rfl

private theorem quotientLevel_coordinates (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T)
    (hχ : ∀ n (M : CochainComplex (Modules l E T) ℤ) k,
      data.χ n M k = eqToIso (congrArg (fun K ↦ K.X k) (data.hobj n M)) ≪≫
        principalConeCoordinates (scalar l E T data.d n M) k)
    (d n : ℕ) (k : ℤ) :
    (quotientLevel l E T data hdata d n).f k =
      (data.χ n (freeComplex l E T d) k).hom ≫ biprod.fst ≫
        (quotientChainMap l E T d n).f k := by
  have he : (mappingCone.descShortComplex
      (ShortComplex.mk (scalar l E T data.d n (freeComplex l E T d))
        (quotientChainMap l E T d n) (chain_ses l E T data hdata d n).choose)).f k =
        (mappingCone.snd (scalar l E T data.d n (freeComplex l E T d))).v k k
          (add_zero k) ≫ (quotientChainMap l E T d n).f k := by
    dsimp only [mappingCone.descShortComplex]
    rw [mappingCone.desc_f _ _ _ _ k (k + 1) rfl]
    simp only [HomComplex.Cochain.zero_v, comp_zero, zero_add]
  rw [hχ]
  have ht := CoefficientCone.cone_transport_coordinates
    (data.hobj n (freeComplex l E T d)) rfl
    (mappingCone.descShortComplex
      (ShortComplex.mk (scalar l E T data.d n (freeComplex l E T d))
        (quotientChainMap l E T d n) (chain_ses l E T data hdata d n).choose))
    k ((quotientChainMap l E T d n).f k) he
  simpa only [quotientLevel, eqToIso_refl, Iso.refl_hom, Category.id_comp] using ht

private theorem quotientLevel_step (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T)
    (hχ : ∀ n (M : CochainComplex (Modules l E T) ℤ) k,
      data.χ n M k = eqToIso (congrArg (fun K ↦ K.X k) (data.hobj n M)) ≪≫
        principalConeCoordinates (scalar l E T data.d n M) k)
    (hT : ∀ n (M : CochainComplex (Modules l E T) ℤ) k,
      ((data.T n).app M).f k ≫ (data.χ n M k).hom =
        (data.χ (n + 1) M k).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E T data.d M).f (k + 1)))
    (d n : ℕ) :
    (data.T n).app (freeComplex l E T d) ≫ quotientLevel l E T data hdata d n =
      quotientLevel l E T data hdata d (n + 1) ≫
        (quotientTower l E T d).asFunctor.map (homOfLE n.le_succ).op := by
  ext1 k
  simp only [HomologicalComplex.comp_f,
    quotientLevel_coordinates l E T data hdata hχ, Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hT]
  simp only [Category.assoc, biprod.map_fst, Category.id_comp]
  rw [← HomologicalComplex.comp_f, quotientChainMap_step]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientLevel_unit (data : PrincipalReductionConeData l E T)
    (hdata : data.IsCanonical l E T)
    (hχ : ∀ n (M : CochainComplex (Modules l E T) ℤ) k,
      data.χ n M k = eqToIso (congrArg (fun K ↦ K.X k) (data.hobj n M)) ≪≫
        principalConeCoordinates (scalar l E T data.d n M) k)
    (hj : ∀ n (M : CochainComplex (Modules l E T) ℤ) k,
      ((data.j n).app M).f k ≫ (data.χ n M k).hom = biprod.inl)
    (d n : ℕ) :
    (data.j n).app (freeComplex l E T d) ≫ quotientLevel l E T data hdata d n =
      quotientChainMap l E T d n := by
  ext1 k
  simp only [HomologicalComplex.comp_f,
    quotientLevel_coordinates l E T data hdata hχ]
  rw [← Category.assoc, ← Category.assoc, hj]
  simp

section
attribute [local irreducible] freeComplex

private theorem strict_quotient_comparison (d : ℕ)
    (data : PrincipalReductionConeData l E T) (hdata : data.IsCanonical l E T) :
    ∃ q : (CompletionTriangle.tower l E T data).obj (freeComplex l E T d) ⟶
        quotientTower l E T d,
      (∀ n : ℕ, QuasiIso
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n))) ∧
      (∀ (n : ℕ) (k : ℤ), (q.f k).app (op n) =
        (data.χ n (freeComplex l E T d) k).hom ≫ biprod.fst ≫
          (quotientChainMap l E T d n).f k) ∧
      (∀ n : ℕ, (data.j n).app (freeComplex l E T d) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n) =
          quotientChainMap l E T d n) := by
  obtain ⟨sD, sR, κR, Φ, hχ, hmap, hT, hj, hjT, hq, htri, hκT, hκj,
      hΦ, hsD, hnatΦ, hTΦ, hTs, hinc, hboundary, haugΦ, haugs, hκs⟩ :=
    (hdata (op (Profinite.of (ULift.{u} Unit))) 0 ⟨()⟩).2
  let f : ((CompletionTriangle.tower l E T data).obj
      (freeComplex l E T d)).asFunctor ⟶ (quotientTower l E T d).asFunctor :=
    NatTrans.ofOpSequence (quotientLevel l E T data hdata d) (fun n ↦ by
      rw [CompletionTriangle.tower_step]
      exact quotientLevel_step l E T data hdata hχ hT d n)
  let q : (CompletionTriangle.tower l E T data).obj (freeComplex l E T d) ⟶
      quotientTower l E T d :=
    { f := fun k ↦
        { app := fun n ↦ (f.app n).f k
          naturality := fun _ _ g ↦ congrArg (fun a ↦ a.f k) (f.naturality g) }
      comm' := fun k r _ ↦ NatTrans.ext (funext (fun n ↦ (f.app n).comm k r)) }
  refine ⟨q, ?_, ?_, ?_⟩
  · intro n
    exact quotientLevel_quasiIso l E T data hdata d n
  · intro n k
    exact quotientLevel_coordinates l E T data hdata hχ d n k
  · intro n
    exact quotientLevel_unit l E T data hdata hχ hj d n

end

attribute [local irreducible] quotientLevel

private def quotientAugmentation (d : ℕ) :
    freeComplex l E T d ⟶ roosF.obj (quotientTower l E T d) :=
  roosAugment (quotientChainMap l E T d) (quotientChainMap_step l E T d)

private theorem quotientAugmentation_coordinates (d : ℕ) (p : ℤ) :
    (quotientAugmentation l E T d).f (p + 1) ≫
        (roosχ (quotientTower l E T d) p).hom =
      biprod.lift 0 ((Pi.lift (quotientChainMap l E T d)).f (p + 1)) :=
  roosAugment_χ _ _ p

private def quotientCone (d : ℕ) : Cone (quotientTower l E T d).asFunctor :=
  ⟨freeComplex l E T d, NatTrans.ofOpSequence (quotientChainMap l E T d)
    (fun n ↦ by simpa using (quotientChainMap_step l E T d n).symm)⟩

private def powerSingle (d : ℕ) : Modules l E T ⥤ CochainComplex (Modules l E T) ℤ :=
  finiteBiproductPower (A := Modules l E T) d ⋙ (singleFunctor (Modules l E T) 0)

private instance powerSingleLimits (d : ℕ) :
    PreservesLimitsOfShape ℕᵒᵖ (powerSingle l E T d) := by
  unfold powerSingle
  have : PreservesLimitsOfShape ℕᵒᵖ (singleFunctor (Modules l E T) 0) :=
    HomologicalComplex.instPreservesLimitsOfShapeSingle (C := Modules l E T)
      (c := .up ℤ) 0
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def functorComplexIso {A J : Type*} [Category A] [Category J]
    [HasZeroMorphisms A] (F : J ⥤ CochainComplex A ℤ) :
    (complexOfSequence F).asFunctor ≅ F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    dsimp only [Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    apply HomologicalComplex.Hom.ext
    funext k
    rfl)

private def quotientDiagramIso (d : ℕ) :
    (quotientTower l E T d).asFunctor ≅ coefficientSequence l E T ⋙ powerSingle l E T d :=
  functorComplexIso (quotientSequence l E T d)

private theorem quotientDiagramIso_app (d : ℕ) (n : ℕᵒᵖ) :
    (quotientDiagramIso l E T d).hom.app n = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def quotientConeIso (d : ℕ) :
    (powerSingle l E T d).mapCone (coefficientCone l E T) ≅
      (Cone.postcompose (quotientDiagramIso l E T d).hom).obj
        (quotientCone l E T d) := by
  refine Cone.ext (Iso.refl _) ?_
  intro n
  dsimp only [Cone.postcompose, Functor.mapCone, Cone.extend, NatTrans.comp_app]
  rw [quotientDiagramIso_app]
  simp only [Category.comp_id]
  rfl

private theorem quotientCone_isLimit (d : ℕ) :
    Nonempty (IsLimit (quotientCone l E T d)) :=
  ⟨(IsLimit.postcomposeHomEquiv (quotientDiagramIso l E T d) _).toFun
    ((isLimitOfPreserves (powerSingle l E T d)
      (integral_coefficient_quotient_limit l E T).1.some).ofIsoLimit
        (quotientConeIso l E T d))⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotientTower_epi (d : ℕ) (p : ℤ) (n : ℕ) :
    Epi (((quotientTower l E T d).X p).map (homOfLE n.le_succ).op) := by
  let F := finiteBiproductPower (A := Modules l E T) d
  let S := HomologicalComplex.single (Modules l E T) (.up ℤ) 0
  have : F.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels F
  have : Epi ((DerivedNakayama.pullback l E T).map (quotientStep l E n)) := by
    simpa only [coefficientSequence, Functor.ofOpSequence_map_homOfLE_succ] using
      (integral_coefficient_quotient_limit l E T).2 n
  have : Epi (S.map (F.map
      ((DerivedNakayama.pullback l E T).map (quotientStep l E n)))) := by
    infer_instance
  change Epi (((quotientSequence l E T d).map (homOfLE n.le_succ).op).f p)
  rw [quotientSequence_step]
  change Epi ((S.map (F.map
    ((DerivedNakayama.pullback l E T).map (quotientStep l E n)))).f p)
  infer_instance

attribute [local irreducible] quotientTower

private theorem quotientAugmentation_quasiIso (d : ℕ) :
    QuasiIso (quotientAugmentation l E T d) := by
  exact roosAugment_quasiIso (quotientCone l E T d)
    (quotientCone_isLimit l E T d).some (quotientChainMap l E T d)
    (quotientChainMap_step l E T d) (fun _ ↦ rfl)
    (roosU_degreewise_epi
      (Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
      (quotientTower_epi l E T d))

section
attribute [local irreducible] freeComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_comparison (d : ℕ)
    (data : PrincipalReductionConeData l E T)
    (q : (CompletionTriangle.tower l E T data).obj (freeComplex l E T d) ⟶
      quotientTower l E T d)
    (hq : ∀ n : ℕ, (data.j n).app (freeComplex l E T d) ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n) =
        quotientChainMap l E T d n)
    (a : 𝟭 (CochainComplex (Modules l E T) ℤ) ⟶
      CompletionTriangle.complexCompletion l E T data)
    (ha : ∀ p : ℤ, (a.app (freeComplex l E T d)).f (p + 1) ≫
      (roosχ ((CompletionTriangle.tower l E T data).obj (freeComplex l E T d)) p).hom =
        biprod.lift 0 ((Pi.lift
          (f := fun n : ℕ ↦ ((CompletionTriangle.tower l E T data).obj
            (freeComplex l E T d)).asFunctor.obj (op n))
          (fun n : ℕ ↦ (data.j n).app (freeComplex l E T d))).f (p + 1))) :
    a.app (freeComplex l E T d) ≫ roosF.map q = quotientAugmentation l E T d := by
  apply HomologicalComplex.Hom.ext
  funext k
  suffices ∀ p : ℤ,
      (a.app (freeComplex l E T d) ≫ roosF.map q).f (p + 1) =
        (quotientAugmentation l E T d).f (p + 1) from forall_int_next
    (P := fun r ↦ (a.app (freeComplex l E T d) ≫ roosF.map q).f r =
      (quotientAugmentation l E T d).f r) this k
  intro p
  apply (cancel_mono (roosχ (quotientTower l E T d) p).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ]
  rw [← Category.assoc, ha, quotientAugmentation_coordinates]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    rw [← HomologicalComplex.comp_f]
    congr 1
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, roosPmap, Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact hq n

end

section
attribute [local irreducible] freeComplex

private theorem free_complete (d : ℕ) :
    IsDerivedComplete l E T (DerivedCategory.Q.obj (freeComplex l E T d)) := by
  obtain ⟨data, hdata, a, F, c, κ, sF, hadd, ha, hc, hrep, hcomplete, hshift, htri⟩ :=
    CompletionTriangle.completion_triangle_comparison l E T
  obtain ⟨q, hq, hcoord, hj⟩ := strict_quotient_comparison l E T d data hdata
  have : CountableAB4Star (Modules l E T) := CompletionTriangle.countableExact l E T
  have : QuasiIso (roosF.map q) := (RoosConeCalculus.assemble_calculus).2.2.1 q hq
  have hb : QuasiIso (quotientAugmentation l E T d) :=
    quotientAugmentation_quasiIso l E T d
  have hcomp : IsIso (DerivedCategory.Q.map (a.app (freeComplex l E T d)) ≫
      DerivedCategory.Q.map (roosF.map q)) := by
    rw [← Functor.map_comp, augmentation_comparison l E T d data q hj a (ha _)]
    infer_instance
  have hi : IsIso (DerivedCategory.Q.map (a.app (freeComplex l E T d))) :=
    IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map (roosF.map q))
  apply (hcomplete _).mpr
  have : IsIso (c.app (DerivedCategory.Q.obj (freeComplex l E T d)) ≫
      κ.hom.app (freeComplex l E T d)) := by rw [hc]; exact hi
  exact IsIso.of_isIso_comp_right _ (κ.hom.app (freeComplex l E T d))

end

section
attribute [local irreducible] freeComplex

/-- Finite constant scalar local models are complete, including global models and
finite free powers. In the free case the strict cone-to-quotient map is fixed in
coordinates, is a quasi-isomorphism at every level, and respects the augmentations.
The derived isomorphism to the quotient Roos limit has exactly the scalar quotient
projections. Every strict completion augmentation with the coordinate formula of
`completion_triangle_comparison` maps to this cone under the Roos image of that same
strict tower map q; thus the comparison carries the specified completion unit to it.

Source: blueprint main-20261015, localizing-closure-ctf-equals-bc, Local models and
Locality; Bhatt--Scholze, Propositions 3.1.9--3.1.10 and Section 3.4
(blueprint: lem-sfb-finite-scalar-local-model-complete).

Proof:
1. The integral coefficient comparison identifies B with the inverse limit of k_n,
   and flatness over the constant DVR gives the short exact scalar cyclic resolution.
   Apply its d-fold power and the cone/short-exact quasi-isomorphism. The cone map
   is quotient on the unshifted coordinate and zero on the shifted coordinate.
   It intertwines (x,y) -> (x,pi*y) with the actual quotient transition and sends
   (x,0) to x modulo pi^(n+1). This gives the single strict tower map q below.
2. The quotient transitions are epimorphisms. The surjective pro-etale tower lemma
   gives the exact Roos sequence; coordinatewise integral comparison identifies its
   kernel with B^d and its projections with the scalar quotients. The Roos functor
   carries q to a quasi-isomorphism and its augmentation to (quotients,0).
   The completion triangle comparison identifies that augmentation with the specified
   completion unit. Its coordinate formula and the Roos image of that same q give
   a.app B^d[0] ≫ roosF.map q = b. Localizing gives the normalized isomorphism e
   with e.hom = Q.map b; the augmentation comparison therefore uses q itself.
   For d=0 all these objects and maps are zero.
3. A finitely presented scalar module over the DVR has a length-one finite free
   resolution. The scalar-model finite-flat-resolution lemma and coefficient flatness
   give the corresponding short exact sequence over B, without torsion-freeness.
   Its degree-zero triangle, and the exact completion functor with its natural unit,
   give a morphism of distinguished triangles including the boundary square.
   The free case and two-out-of-three make the third unit invertible. This proves
   the global scalar-model assertion, including torsion modules and zero.
4. Over a covering object the weakly-etale localization equivalence identifies
   restriction with slice restriction; coefficient-sections localization identifies
   the actual coefficient rings and scalar maps. Exact slice restriction preserves
   sectionwise products, finite sums, cones, the principal tower transitions and
   augmentation, hence the Roos construction and completion unit. This gives the
   completion comparison on covering slices, without asserting product preservation
   for arbitrary geometric inverse image.
5. Restrict a local model and its unit to each member of its pro-etale covering.
   Naturality transports that unit through the model isomorphism to the global
   scalar-model unit of step 3. Covering restrictions jointly reflect isomorphisms
   in the unbounded derived category, so the original unit is invertible. No qcqs,
   Noetherian, dimension or characteristic hypothesis is used. -/
theorem finite_scalar_local_model_complete :
    (∀ M : Modules l E T,
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) T M →
        IsDerivedComplete l E T
          (DerivedCategory.Q.obj ((singleFunctor (Modules l E T) 0).obj M))) ∧
    (∀ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P →
        IsDerivedComplete l E T (DerivedCategory.Q.obj
          ((singleFunctor (Modules l E T) 0).obj
            ((DerivedNakayama.pullback l E T).obj P)))) ∧
    (∀ d : ℕ,
      IsDerivedComplete l E T (DerivedCategory.Q.obj (freeComplex l E T d)) ∧
      ∀ data : PrincipalReductionConeData l E T, data.IsCanonical l E T →
      ∃ (q : (CompletionTriangle.tower l E T data).obj (freeComplex l E T d) ⟶
          quotientTower l E T d)
        (b : freeComplex l E T d ⟶ roosF.obj (quotientTower l E T d))
        (e : DerivedCategory.Q.obj (freeComplex l E T d) ≅
          DerivedCategory.Q.obj (roosF.obj (quotientTower l E T d))),
        (∀ n : ℕ, QuasiIso
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n))) ∧
        (∀ (n : ℕ) (k : ℤ), (q.f k).app (op n) =
          (data.χ n (freeComplex l E T d) k).hom ≫ biprod.fst ≫
            (quotientChainMap l E T d n).f k) ∧
        (∀ n : ℕ, (data.j n).app (freeComplex l E T d) ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n) =
            quotientChainMap l E T d n) ∧
        (∀ p : ℤ, b.f (p + 1) ≫ (roosχ (quotientTower l E T d) p).hom =
          biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ quotientChainMap l E T d n)).f (p + 1))) ∧
        e.hom = DerivedCategory.Q.map b ∧
        (∀ a : 𝟭 (CochainComplex (Modules l E T) ℤ) ⟶
            CompletionTriangle.complexCompletion l E T data,
          (∀ p : ℤ, (a.app (freeComplex l E T d)).f (p + 1) ≫
            (roosχ ((CompletionTriangle.tower l E T data).obj
              (freeComplex l E T d)) p).hom =
              biprod.lift 0 ((Pi.lift
                (f := fun n : ℕ ↦ ((CompletionTriangle.tower l E T data).obj
                  (freeComplex l E T d)).asFunctor.obj (op n))
                (fun n : ℕ ↦ (data.j n).app (freeComplex l E T d))).f (p + 1))) →
          a.app (freeComplex l E T d) ≫ roosF.map q = b)) := by
  have hfree (X : Scheme.{u}) (d : ℕ) := free_complete l E X d
  have hlocal := local_complete_of_free l E T hfree
  refine ⟨hlocal, point_complete_of_local l E T hlocal, ?_⟩
  intro d
  refine ⟨hfree T d, ?_⟩
  intro data hdata
  obtain ⟨q, hq, hcoord, hj⟩ := strict_quotient_comparison l E T d data hdata
  have : QuasiIso (quotientAugmentation l E T d) :=
    quotientAugmentation_quasiIso l E T d
  refine ⟨q, quotientAugmentation l E T d,
    asIso (DerivedCategory.Q.map (quotientAugmentation l E T d)),
    hq, hcoord, hj, quotientAugmentation_coordinates l E T d, rfl, ?_⟩
  intro a ha
  exact augmentation_comparison l E T d data q hj a ha

end

end AlgebraicGeometry.ProEtale.FiniteScalarCompletion
