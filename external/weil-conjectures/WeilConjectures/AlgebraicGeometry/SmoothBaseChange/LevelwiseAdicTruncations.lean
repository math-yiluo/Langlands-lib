/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorCohomologicalBounds
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.Regular.RegularQuotientSelfCohomology
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalAdjacentQuotientTor
import all WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralLocalReductionLowerBound
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedConstructibleTowerLocalEffectivity
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
import all WeilConjectures.AlgebraicGeometry.SmoothBaseChange.ActualCompletedReductionReconstruction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement

/-!
# Levelwise truncations of an adic reduction tower

Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1429;
Stacks Tags 0118, 08J5, 09C1, 09C7, 099M, 099N and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).

The strict tower and its quotient-linear levels remain distinct. Standard truncations
are Mathlib's canonical functors. The output data retain both exact evaluation comparisons
and the normalization of the entire truncation triangle. Higher Tor vanishing is required
only for normalization, never for the unconditional strict-tower cohomology formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private local instance : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

-- Select the generic standard localizations before trying specialized coefficient instances.
attribute [local instance 2000] reductionRingModulesHasDerivedCategory
attribute [local instance 2000] pbcTowers_hasDerivedCategory

-- Keep the universal scalar-extension witnesses behind their functor/adjunction API.
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
attribute [local irreducible] pbcDerivedRestrictComp pbcRestrictComp pbcScalarAdjunction
attribute [local irreducible] Functor.mapDerivedCategory completedReductionCoefficient
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint
attribute [local irreducible] pbcComplexCounit pbcExtensionCounit

/-- Exact scalar restriction inherits the existing termwise derived shift comparison.
Source: Stacks Tag 03DA, blueprint order 1429
(blueprint: prop-weil-pbc-levelwise-truncations). -/
instance pbcLevelwiseRestrictionCommShift
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedRestrict φ).CommShift ℤ :=
  inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)

/-- The scalar-extension shift comparison is the canonical mate of exact restriction's
specified shift comparison under the tensor-unit normalized adjunction.
Source: Stacks Tag 06YY, blueprint order 1429
(blueprint: prop-weil-pbc-levelwise-truncations). -/
instance pbcLevelwiseScalarCommShift
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).CommShift ℤ :=
  (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ

/-- The higher-Tor condition at precisely the degrees above the cutoff. The module
H^q(M_(n + 1)) is placed in degree zero before scalar extension; positive p means degree -p.
Source: blueprint order 1429, (TC); Stacks Tag 06YU
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTorVanishing (M : AdicTower T d) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (q : ℤ), m + 1 ≤ q → ∀ p : ℕ, 0 < p →
    IsZero ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level (n + 1))))))

/-- Both adic truncations, retaining the actual strict tower, canonical quotient-linear
levels, and their canonical exact evaluation comparisons. These equalities specify
objects, not additional hypotheses on the input.
Source: blueprint order 1429, (1) and (3); Stacks Tags 0118 and 08J5
(blueprint: prop-weil-pbc-levelwise-truncations). -/
structure PbcLevelwiseTruncationData (M : AdicTower T d) (m : ℤ) where
  /-- The lower normalized tower, with its transitions and full quotient cocycle. -/
  lower : AdicTower T d
  /-- The upper normalized tower, with its transitions and full quotient cocycle. -/
  upper : AdicTower T d
  /-- The underlying strict tower is its canonical lower truncation. -/
  lowerTower : lower.tower = (DerivedCategory.TStructure.t.truncLE m).obj M.tower
  /-- The underlying strict tower is its canonical upper truncation. -/
  upperTower : upper.tower = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower
  /-- The quotient-linear lower levels are the canonical truncations. -/
  lowerLevel : ∀ n : ℕ,
    lower.level n = (DerivedCategory.TStructure.t.truncLE m).obj (M.level n)
  /-- The quotient-linear upper levels are the canonical truncations. -/
  upperLevel : ∀ n : ℕ,
    upper.level n = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)
  /-- Evaluation uses the specified exact-functor and original evaluation comparisons. -/
  lowerEvaluation : ∀ n : ℕ,
    lower.evaluation n ≪≫ (pbcTowerEvaluation T (pbcAdicCompletion T d) n).mapIso
        (eqToIso lowerTower) =
      (pbcDerivedRestrict (pbcAdicProjection T d n)).mapIso (eqToIso (lowerLevel n)) ≪≫
        ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncLEIso m).app
          (M.level n) ≪≫
        (DerivedCategory.TStructure.t.truncLE m).mapIso (M.evaluation n) ≪≫
        (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
          (op n)).mapDerivedCategoryTruncLEIso m).symm.app M.tower
  /-- The same canonical evaluation normalization for the upper levels. -/
  upperEvaluation : ∀ n : ℕ,
    upper.evaluation n ≪≫ (pbcTowerEvaluation T (pbcAdicCompletion T d) n).mapIso
        (eqToIso upperTower) =
      (pbcDerivedRestrict (pbcAdicProjection T d n)).mapIso (eqToIso (upperLevel n)) ≪≫
        ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncGEIso (m + 1)).app
          (M.level n) ≪≫
        (DerivedCategory.TStructure.t.truncGE (m + 1)).mapIso (M.evaluation n) ≪≫
        (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
          (op n)).mapDerivedCategoryTruncGEIso (m + 1)).symm.app M.tower

variable {T d}

/-- Lower normalization expressed at the canonical truncation objects.
Source: blueprint order 1429, (1) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTruncationData.lowerNormalization {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj (M.level a) :=
  (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
      (eqToIso (N.lowerLevel b)).symm ≪≫
    N.lower.normalization b a hab ≪≫ eqToIso (N.lowerLevel a)

/-- Upper normalization expressed at the canonical truncation objects.
Source: blueprint order 1429, (1) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTruncationData.upperNormalization {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a) :=
  (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
      (eqToIso (N.upperLevel b)).symm ≪≫
    N.upper.normalization b a hab ≪≫ eqToIso (N.upperLevel a)

variable (T d)

/-- The end normalizations identify the entire reduced truncation triangle, including
its connecting arrow, with the canonical triangle at the lower level. Uniqueness with
the given middle normalization specifies the canonical comparison, also for equal levels.
Source: blueprint order 1429, (1); Stacks Tag 08J5; BBD 1.1.9 and 1.1.10(ii)
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcIsLevelwiseTruncation {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) : Prop :=
  ∀ (b a : ℕ) (hab : a ≤ b),
    ∃! e : (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapTriangle.obj
          ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level b)) ≅
        (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level a),
      e.hom.hom₁ = (N.lowerNormalization b a hab).hom ∧
      e.hom.hom₂ = (M.normalization b a hab).hom ∧
      e.hom.hom₃ = (N.upperNormalization b a hab).hom

/-- The lower-truncated strict semilinear transition, without (TC). Exact scalar
restriction supplies the canonical coefficient-linear truncation comparison.
Source: blueprint order 1429, (3) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedTransitionLE (M : AdicTower T d) (m : ℤ) (b a : ℕ) (hab : a ≤ b) :
    (DerivedCategory.TStructure.t.truncLE m).obj (M.level b) ⟶
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level a)) :=
  (DerivedCategory.TStructure.t.truncLE m).map
      (adicTowerSemilinearTransition T d M.level M.normalization b a hab) ≫
    ((pbcRestrict (pbcAdicQuotient T d b a hab)).mapDerivedCategoryTruncLEIso m).inv.app
      (M.level a)

/-- The upper-truncated strict semilinear transition, without (TC).
Source: blueprint order 1429, (3) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedTransitionGE (M : AdicTower T d) (m : ℤ) (b a : ℕ) (hab : a ≤ b) :
    (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b) ⟶
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)) :=
  (DerivedCategory.TStructure.t.truncGE (m + 1)).map
      (adicTowerSemilinearTransition T d M.level M.normalization b a hab) ≫
    ((pbcRestrict (pbcAdicQuotient T d b a hab)).mapDerivedCategoryTruncGEIso (m + 1)).inv.app
      (M.level a)

set_option backward.isDefEq.respectTransparency false in
private lemma truncLE_restriction_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (F.mapDerivedCategoryTruncLEIso m).inv.app X ≫
        F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app X) =
      (DerivedCategory.TStructure.t.truncLEι m).app (F.mapDerivedCategory.obj X) := by
  have := F.isLE_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.truncLE m).obj X) m
  apply (cancel_epi ((F.mapDerivedCategoryTruncLEIso m).hom.app X)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (DerivedCategory.TStructure.t.liftTruncLE_ι _ m).symm

private lemma truncLE_comparison_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (F.mapDerivedCategoryTruncLEIso m).hom.app X ≫
        (DerivedCategory.TStructure.t.truncLEι m).app (F.mapDerivedCategory.obj X) =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app X) := by
  apply (cancel_epi ((F.mapDerivedCategoryTruncLEIso m).inv.app X)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  exact (truncLE_restriction_counit F X m).symm

set_option backward.isDefEq.respectTransparency false in
private lemma truncGE_restriction_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ m).app (F.mapDerivedCategory.obj X) ≫
        (F.mapDerivedCategoryTruncGEIso m).inv.app X =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app X) := by
  have : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE m ⋙ F.mapDerivedCategory).obj X) m :=
    F.isGE_mapDerivedCategory_obj ((DerivedCategory.TStructure.t.truncGE m).obj X) m
  exact DerivedCategory.TStructure.t.π_descTruncGE _ m

set_option backward.isDefEq.respectTransparency false in
/-- Unconditional cohomology at the quotient-linear levels, and its naturality for
the strict transitions. The maps are H of the canonical truncation counit and unit;
their squares with all semilinear transitions commute before taking cohomology.
Source: blueprint order 1429, (3); Stacks Tag 0118
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: kernels and cokernels in the strict tower category are levelwise. Good truncation
therefore evaluates to good truncation at each level. Its cohomology formulas make
the indicated canonical maps invertible in the surviving range and give zero otherwise.
Functoriality of truncation and exact restriction prove both transition squares.
The formulas also show preservation of levelwise quasi-isomorphisms, so these are
statements in the derived category, not just in chosen complexes. -/
theorem pbc_levelwise_truncation_cohomology (M : AdicTower T d) (m : ℤ) :
    (∀ (n : ℕ) (i : ℤ), i ≤ m →
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), m < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), m + 1 ≤ i →
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), i ≤ m →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)))) ∧
    ∀ (b a : ℕ) (hab : a ≤ b),
      (DerivedCategory.TStructure.t.truncLEι m).app (M.level b) ≫
          adicTowerSemilinearTransition T d M.level M.normalization b a hab =
        pbcTruncatedTransitionLE T d M m b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            ((DerivedCategory.TStructure.t.truncLEι m).app (M.level a)) ∧
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level a)) =
        (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b) ≫
          pbcTruncatedTransitionGE T d M m b a hab := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
      (M.level n) (m + 1) i (by omega)
  · intro n i hi
    exact DerivedCategory.isZero_of_isLE _ m i hi
  · intro n i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app (M.level n) _ i hi
  · intro n i hi
    exact DerivedCategory.isZero_of_isGE _ (m + 1) i (by omega)
  · intro b a hab
    constructor
    · dsimp only [pbcTruncatedTransitionLE, pbcDerivedRestrict]
      rw [Category.assoc, truncLE_restriction_counit]
      exact ((DerivedCategory.TStructure.t.truncLEι m).naturality _).symm
    · dsimp only [pbcTruncatedTransitionGE, pbcDerivedRestrict]
      rw [← Category.assoc, ← NatTrans.naturality]
      simp only [Functor.id_map, Category.assoc]
      rw [truncGE_restriction_unit]

section ReductionTowerPresentation

-- Compare the completed-coefficient aliases without expanding the chosen limit cone.
attribute [local semireducible] completedReductionCoefficient
attribute [local irreducible] CategoryTheory.Limits.limit

/-- The fixed K-flat evaluation comparison for the reduction of one completed object.
Source: blueprint order 1429, opening paragraph; Stacks Tag 06YY
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcReductionEvaluationIso (K : PbcCompletedDerived T d) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
        ((pbcCompletedReduction T d n).obj K) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((completedReductionTower T d).obj K) :=
  (asIso (completedReductionEvaluation T d n)).symm.app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_complex_counit_eq
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules T R) ℤ) :
    pbcComplexCounit φ P = reductionScalarComplexCounit T φ P := by
  unfold pbcComplexCounit pbcExtensionCounit reductionScalarComplexCounit
    reductionComplexCounit
  rfl

section ReductionLaws

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_restriction_coherence
    {R S B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : B ⟶ C)
    (π : R ⟶ B) (τ : S ⟶ C) (ρ : R ⟶ C)
    (h₁ : φ ≫ ψ = π) (h₂ : ψ ≫ χ = τ)
    (h₃ : φ ≫ τ = ρ) (h₄ : π ≫ χ = ρ) :
    Functor.whiskerRight (pbcDerivedRestrictComp ψ χ τ h₂).hom
        (pbcDerivedRestrict φ) ≫ (pbcDerivedRestrictComp φ τ ρ h₃).hom =
      Functor.whiskerLeft (pbcDerivedRestrict χ)
        (pbcDerivedRestrictComp φ ψ π h₁).hom ≫
          (pbcDerivedRestrictComp π χ ρ h₄).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (pbcModules T C) (.up ℤ))
  intro P
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply (cancel_mono ((pbcRestrict ρ).mapDerivedCategoryFactors.hom.app P)).1
  simp only [Category.assoc]
  erw [reconstructionRestrictionFactors T φ τ ρ h₃,
    reconstructionRestrictionFactors T π χ ρ h₄]
  erw [← Functor.map_comp_assoc, reconstructionRestrictionFactors T ψ χ τ h₂]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [pbcDerivedRestrict, Functor.comp_obj] at *
  have hn := (pbcDerivedRestrictComp φ ψ π h₁).hom.naturality
    ((pbcRestrict χ).mapDerivedCategoryFactors.hom.app P)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  dsimp only [pbcDerivedRestrict, Functor.comp_obj] at *
  erw [reassoc_of% (reconstructionRestrictionFactors T φ ψ π h₁
    (((pbcRestrict χ).mapHomologicalComplex (.up ℤ)).obj P))]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map, ← DerivedCategory.Q.map_comp]
  congr 4
  apply HomologicalComplex.Hom.ext
  funext i
  ext U x
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  change ((pbcRestrictComp φ τ ρ h₃).hom.app (P.X i)).val.app U
      (((pbcRestrictComp ψ χ τ h₂).hom.app (P.X i)).val.app U x) =
    ((pbcRestrictComp π χ ρ h₄).hom.app (P.X i)).val.app U
      (((pbcRestrictComp φ ψ π h₁).hom.app ((pbcRestrict χ).obj (P.X i))).val.app U x)
  erw [reconstructionComp_section, reconstructionComp_section,
    reconstructionComp_section, reconstructionComp_section]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_transition_cocycle
    {R S B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : B ⟶ C)
    (π : R ⟶ B) (τ : S ⟶ C) (ρ : R ⟶ C)
    (h₁ : φ ≫ ψ = π) (h₂ : ψ ≫ χ = τ)
    (h₃ : φ ≫ τ = ρ) (h₄ : π ≫ χ = ρ)
    (K : DerivedCategory (pbcModules T R)) :
    pbcReductionTransition φ τ ρ h₃ K =
      pbcReductionTransition φ ψ π h₁ K ≫
        (pbcDerivedRestrict ψ).map (pbcReductionTransition π χ ρ h₄ K) ≫
          (pbcDerivedRestrictComp ψ χ τ h₂).hom.app ((pbcDerivedExtend ρ).obj K) := by
  have hc := congr_app (reduction_restriction_coherence T φ ψ χ π τ ρ h₁ h₂ h₃ h₄)
    ((pbcDerivedExtend ρ).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hc
  apply ((pbcDerivedScalarAdjunction φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  rw [pbcReductionTransition, Equiv.apply_symm_apply]
  rw [pbcReductionTransition, Equiv.apply_symm_apply]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ π h₁).inv.naturality
    (pbcReductionTransition π χ ρ h₄ K)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← Category.assoc]
  rw [← (pbcDerivedScalarAdjunction π).homEquiv_unit]
  rw [pbcReductionTransition, Equiv.apply_symm_apply]
  apply (cancel_mono ((pbcDerivedRestrictComp φ τ ρ h₃).hom.app
    ((pbcDerivedExtend ρ).obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hc]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_module_tower_map
    (M : pbcModules T (pbcAdicCompletion T d)) (b a : ℕ) (hab : a ≤ b) :
    (completedReductionModuleTower T d M).map (homOfLE hab).op =
      (completedReductionTransition T d b a hab).app M := by
  apply level_hom_ext T (pbcAdicProjection T d b) M
  intro U s x
  erw [(completedReductionTransition_exists T d b a hab).exists.choose_spec M U s x]
  induction b, hab using Nat.le_induction with
  | base =>
      have hi : (homOfLE (le_refl a)).op = 𝟙 (op a) := Subsingleton.elim _ _
      rw [hi, (completedReductionModuleTower T d M).map_id]
      change reductionTensorSection T _ M U s x = _
      rw [reductionCoefficientMap_id]
      rfl
  | succ b hab ih =>
      have hc : (homOfLE (hab.trans (Nat.le_succ b))).op =
          (homOfLE (Nat.le_succ b)).op ≫ (homOfLE hab).op := Subsingleton.elim _ _
      rw [hc, Functor.map_comp]
      erw [show (completedReductionModuleTower T d M).map
          (homOfLE (Nat.le_succ b)).op =
          (completedReductionTransition T d (b + 1) b (Nat.le_succ b)).app M from
        Functor.ofOpSequence_map_homOfLE_succ _ b]
      change ((completedReductionModuleTower T d M).map (homOfLE hab).op).val.app U
        (((completedReductionTransition T d (b + 1) b (Nat.le_succ b)).app M).val.app U
          (reductionTensorSection T _ M U s x)) = _
      erw [(completedReductionTransition_exists T d (b + 1) b
        (Nat.le_succ b)).exists.choose_spec M U s x, ih]
      congr 1
      exact (ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U)
        (pbcAdicQuotient_comp T d (b + 1) b a hab (Nat.le_succ b))) s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_allpair_comparison (b a : ℕ) (hab : a ≤ b) :
    let step : pbcCompletedReduction T d b ⋙
        pbcDerivedRestrict (pbcAdicProjection T d b) ⟶
      pbcCompletedReduction T d a ⋙ pbcDerivedRestrict (pbcAdicProjection T d a) :=
      { app K := (pbcDerivedRestrict (pbcAdicProjection T d b)).map
          (pbcReductionTransition (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) ≫
          (pbcDerivedRestrictComp (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab)).hom.app
              ((pbcCompletedReduction T d a).obj K)
        naturality := by
          intro K L f
          dsimp only [Functor.comp_map]
          simp only [← Category.assoc, ← Functor.map_comp]
          rw [reconstructionTransition_natural T]
          simp only [Functor.map_comp, Category.assoc]
          exact congrArg (fun t ↦ _ ≫ t)
            ((pbcDerivedRestrictComp (pbcAdicProjection T d b)
              (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
              (pbcAdicProjection_comp T d b a hab)).hom.naturality
                ((pbcCompletedReduction T d a).map f)) }
    let strictStep := Functor.whiskerLeft (completedReductionTower T d)
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab)
    strictStep ≫ completedReductionEvaluation T d a =
      completedReductionEvaluation T d b ≫ step := by
  intro step strictStep
  apply derived_natTrans_ext _ _
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d) P)
    (fun X ↦ by
      obtain ⟨P, p, hk, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients
          (R := completedReductionCoefficient T d) X
      exact ⟨P, p, hk, hp⟩)
  intro P hP
  let φ := pbcAdicProjection T d a
  let c := (pbcDerivedRestrict φ).map (pbcComplexCounit φ P) ≫
    (pbcRestrict φ).mapDerivedCategoryFactors.hom.app
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)
  have : IsIso (pbcComplexCounit φ P) := by
    have := pbcExtensionCounit_isIso φ P hP
    unfold pbcComplexCounit
    infer_instance
  have : IsIso c := by dsimp [c]; infer_instance
  apply (cancel_mono c).1
  simp only [NatTrans.comp_app, Category.assoc]
  have he (i : ℕ) :=
    (completedReductionEvaluation_exists T d i).choose_spec.1.2 P hP
  have hs := reconstructionRestrictedTransition_computation T
    (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) φ
    (pbcAdicProjection_comp T d b a hab) P hP
  let J := (completedReductionComplexTowerFunctor T d).obj P
  let q := completedReductionTowerComplexCounit T d P
  let E (i : ℕ) := pbcTowerEvaluation T (pbcAdicCompletion T d) i
  let F (i : ℕ) := (CategoryTheory.evaluation ℕᵒᵖ
    (pbcModules T (pbcAdicCompletion T d))).obj (op i)
  let τ := pbcTowerTransition T (pbcAdicCompletion T d) b a hab
  let t := (NatTrans.mapHomologicalComplex
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).map
      (homOfLE hab).op) (.up ℤ)).app J
  have ht : τ.app (DerivedCategory.Q.obj J) ≫ (F a).mapDerivedCategoryFactors.hom.app J =
      (F b).mapDerivedCategoryFactors.hom.app J ≫ DerivedCategory.Q.map t := by
    dsimp only [τ, pbcTowerTransition]
    erw [Localization.liftNatTrans_app]
    simp only [Localization.Lifting.iso, Functor.whiskerRight_app, Category.assoc]
    dsimp only [F, t]
    simp only [Iso.inv_hom_id_app, Category.comp_id]
  have hj :
      (((pbcRestrict (pbcAdicProjection T d b)).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (reconstructionOrdinaryTransitionNat T (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) φ
            (pbcAdicProjection_comp T d b a hab)) (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex (pbcRestrictComp (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) φ
          (pbcAdicProjection_comp T d b a hab)).hom (.up ℤ)).app
            (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P)) = t := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (pbcRestrict (pbcAdicProjection T d b)).map
        (reconstructionOrdinaryTransition T (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab) (P.X i)) ≫
        (pbcRestrictComp (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab)).hom.app
            ((pbcExtend (pbcAdicProjection T d a)).obj (P.X i)) =
      (completedReductionModuleTower T d (P.X i)).map (homOfLE hab).op
    rw [reduction_module_tower_map T d (P.X i) b a hab]
    exact reconstructionOrdinaryStep T d b a hab (P.X i)
  rw [hj] at hs
  simp only [Category.assoc] at hs
  dsimp only [strictStep, Functor.whiskerLeft_app]
  change τ.app _ ≫ (completedReductionEvaluation T d a).app _ ≫ c =
    (completedReductionEvaluation T d b).app _ ≫
      (step).app _ ≫ c
  dsimp only [c]
  simp only [scalar_complex_counit_eq T] at hs ⊢
  erw [he a]
  change _ = (completedReductionEvaluation T d b).app _ ≫
    (((pbcDerivedRestrict (pbcAdicProjection T d b)).map _) ≫ _) ≫ _
  simp only [Category.assoc]
  erw [hs]
  erw [reassoc_of% (he b)]
  have hn := τ.naturality q
  change τ.app _ ≫ (E a).map q ≫ (F a).mapDerivedCategoryFactors.hom.app J = _
  rw [← Category.assoc, ← hn, Category.assoc, ht]; rfl

end ReductionLaws

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical reduction tower satisfies the strict-transition equation and full
quotient cocycle, before any truncation or Tor hypothesis.
Source: blueprint order 1429, opening paragraph; Stacks Tag 06YY
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: use one K-flat representative for K. The ordinary reduction tower, balancing
maps and evaluations from def-weil-pbc-adic-coefficient-datum are computed on this
same representative. The balancing formula s⊗(r⊗x)↦s q(r)⊗x gives the transition
square and its associativity gives the quotient cocycle. The universal derived counits
and the fixed evaluation comparison transport these equalities to K. -/
theorem pbc_reduction_adic_tower_laws (K : PbcCompletedDerived T d) :
    (∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedRestrict (pbcAdicProjection T d b)).map
          (adicTowerSemilinearTransition T d
            (fun n ↦ (pbcCompletedReduction T d n).obj K)
            (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
              (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
              (pbcAdicProjection_comp T d b a hab) K) b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab)).hom.app
            ((pbcCompletedReduction T d a).obj K) ≫
        (pbcReductionEvaluationIso T d K a).hom =
      (pbcReductionEvaluationIso T d K b).hom ≫
        (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app
          ((completedReductionTower T d).obj K)) ∧
    ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) c a (hab.trans hbc) =
        adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) c b hbc ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
            (adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) b a hab) ≫
          (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
            (pbcAdicQuotient T d b a hab) (pbcAdicQuotient T d c a (hab.trans hbc))
            (pbcAdicQuotient_comp T d c b a hab hbc)).hom.app
              ((pbcCompletedReduction T d a).obj K) := by
  have ht (b a : ℕ) (hab : a ≤ b) :
      adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) b a hab =
        pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab) K := by
    change ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).homEquiv _ _)
      (((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).homEquiv _ _).symm
        (pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a hab)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a hab) K)) = _
    exact Equiv.apply_symm_apply _ _
  constructor
  · intro b a hab
    rw [ht]
    have hs := congr_app (reduction_allpair_comparison T d b a hab) K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hs
    have hia : (asIso (completedReductionEvaluation T d a)).inv.app K ≫
        (completedReductionEvaluation T d a).app K = 𝟙 _ :=
      (asIso (completedReductionEvaluation T d a)).inv_hom_id_app K
    have hib : (completedReductionEvaluation T d b).app K ≫
        (asIso (completedReductionEvaluation T d b)).inv.app K = 𝟙 _ :=
      (asIso (completedReductionEvaluation T d b)).hom_inv_id_app K
    dsimp only [pbcReductionEvaluationIso, Iso.symm_hom, Iso.app_hom]
    apply (cancel_epi ((asIso (completedReductionEvaluation T d b)).hom.app K)).1
    apply (cancel_mono ((asIso (completedReductionEvaluation T d a)).hom.app K)).1
    simp only [Category.assoc, asIso_hom, hia, reassoc_of% hib]
    erw [Category.comp_id]
    exact hs.symm
  · intro c b a hab hbc
    rw [ht, ht, ht]
    exact reduction_transition_cocycle T (pbcAdicProjection T d c)
      (pbcAdicQuotient T d c b hbc) (pbcAdicQuotient T d b a hab)
      (pbcAdicProjection T d b) (pbcAdicQuotient T d c a (hab.trans hbc))
      (pbcAdicProjection T d a) (pbcAdicProjection_comp T d c b hbc)
      (pbcAdicQuotient_comp T d c b a hab hbc)
      (pbcAdicProjection_comp T d c a (hab.trans hbc))
      (pbcAdicProjection_comp T d b a hab) K

/-- The actual reduction tower of K: all data come from the recorded K-flat universal
construction and balancing maps; only the two named proof fields are postponed.
Source: blueprint order 1429, opening paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcReductionAdicTower (K : PbcCompletedDerived T d) : AdicTower T d where
  tower := (completedReductionTower T d).obj K
  level n := (pbcCompletedReduction T d n).obj K
  evaluation := pbcReductionEvaluationIso T d K
  normalization b a hab := pbcReductionNormalization (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab) K
  transition := (pbc_reduction_adic_tower_laws T d K).1
  cocycle := (pbc_reduction_adic_tower_laws T d K).2

end ReductionTowerPresentation

attribute [local irreducible] pbcReductionAdicTower

private lemma truncGE_comparison_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app X) ≫
        (F.mapDerivedCategoryTruncGEIso m).hom.app X =
      (DerivedCategory.TStructure.t.truncGEπ m).app (F.mapDerivedCategory.obj X) := by
  apply (cancel_mono ((F.mapDerivedCategoryTruncGEIso m).inv.app X)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simpa only [Category.comp_id] using (truncGE_restriction_unit F X m).symm

private lemma truncated_stepGE_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X : DerivedCategory D} {Y : DerivedCategory C}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ m).app X ≫
        (DerivedCategory.TStructure.t.truncGE m).map f ≫
          (U.mapDerivedCategoryTruncGEIso m).inv.app Y =
      f ≫ U.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app Y) := by
  rw [← Category.assoc, ← (DerivedCategory.TStructure.t.truncGEπ m).naturality f]
  rw [Category.assoc, truncGE_restriction_unit]
  rfl

private lemma truncated_stepLE_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X : DerivedCategory D} {Y : DerivedCategory C}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncLE m).map f ≫
        (U.mapDerivedCategoryTruncLEIso m).inv.app Y ≫
          U.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app Y) =
      (DerivedCategory.TStructure.t.truncLEι m).app X ≫ f := by
  rw [truncLE_restriction_counit]
  exact (DerivedCategory.TStructure.t.truncLEι m).naturality f

section ScalarBounds

attribute [local semireducible] completedAdicDerivedChange

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_truncation_triangle
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (K : DerivedCategory (pbcModules T R)) (L : DerivedCategory (pbcModules T S))
    (e : (pbcDerivedExtend φ).obj K ≅ L) (m : ℤ)
    (hTor : ∀ (q : ℤ), m + 1 ≤ q → ∀ (p : ℕ), 0 < p →
      IsZero ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).obj
        ((pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))))) :
    ∃! τ : (pbcDerivedExtend φ).mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj K) ≅
      (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj L,
      τ.hom.hom₂ = e.hom := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : (pbcDerivedScalarAdjunction φ).CommShift ℤ :=
    (pbcDerivedScalarAdjunction φ).commShift_of_rightAdjoint ℤ
  have : (pbcDerivedRestrict φ).IsTriangulated :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.IsTriangulated)
  have : (pbcDerivedExtend φ).IsTriangulated :=
    (pbcDerivedScalarAdjunction φ).isTriangulated_leftAdjoint
  have hLE : ((pbcDerivedExtend φ).obj
      ((DerivedCategory.TStructure.t.truncLE m).obj K)).IsLE m :=
    (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u} φ m).1
      _ inferInstance
  have hGE : ((pbcDerivedExtend φ).obj
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K)).IsGE (m + 1) := by
    apply (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u}
      φ (m + 1)).2 _ inferInstance
    intro q hq p hp
    let Z := (DerivedCategory.TStructure.t.truncGE (m + 1)).obj K
    have : IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app K)) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K (m + 1) q hq
    let eH : (DerivedCategory.homologyFunctor _ q).obj Z ≅
        (DerivedCategory.homologyFunctor _ q).obj K :=
      (asIso ((DerivedCategory.homologyFunctor _ q).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app K))).symm
    exact (hTor q hq p hp).of_iso
      ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).mapIso
        ((pbcDerivedExtend φ).mapIso
          (((DerivedCategory.singleFunctorIsoCompQ (pbcModules T R) 0).app
              ((DerivedCategory.homologyFunctor _ q).obj Z)).symm ≪≫
            (DerivedCategory.singleFunctor _ 0).mapIso eH)))
  let t := DerivedCategory.TStructure.t (C := pbcModules T S)
  have hs := (pbcDerivedExtend φ).map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished m (m + 1) rfl K)
  have ht := t.triangleLEGE_distinguished m (m + 1) rfl L
  obtain ⟨τ, hτ⟩ := t.triangle_iso_exists hs ht e m (m + 1)
    hLE hGE (by
      change t.IsLE ((t.truncLE m).obj L) m
      infer_instance) (by
      change t.IsGE ((t.truncGE (m + 1)).obj L) (m + 1)
      infer_instance)
  refine ⟨τ, hτ, ?_⟩
  intro σ hσ
  apply Iso.ext
  exact t.triangle_map_ext hs ht m (m + 1) hLE (by
    change t.IsGE ((t.truncGE (m + 1)).obj L) (m + 1)
    infer_instance) (hσ.trans hτ.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restriction_id (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules T R) := by
  let eM (M : pbcModules T R) : (pbcRestrict (𝟙 R)).obj M ≅ M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))
  exact NatIso.ofComponents eM (fun f ↦ by ext U x; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def scalar_id (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcDerivedExtend (𝟙 R) ≅ 𝟭 (DerivedCategory (pbcModules T R)) :=
  (pbcDerivedScalarAdjunction (𝟙 R)).leftAdjointUniq
    ((Adjunction.id).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (restriction_id T R) ≪≫
        Functor.mapDerivedCategoryIdIso (pbcModules T R)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncation_upper_bound (M : AdicTower T d) (m : ℤ)
    (hTor : PbcLevelwiseTorVanishing T d M m) (b a : ℕ) (hab : a ≤ b) :
    ((pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b))).IsGE (m + 1) := by
  induction b, hab using Nat.le_induction with
  | base =>
      have hq : pbcAdicQuotient T d a a (le_refl a) = 𝟙 _ :=
        by exact (pbcAdicRings T d).map_id (op a)
      rw [hq]
      have : DerivedCategory.TStructure.t.IsGE
          ((𝟭 (DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op a))))).obj
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)))
          (m + 1) := by
        change ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)).IsGE (m + 1)
        infer_instance
      exact DerivedCategory.TStructure.t.isGE_of_iso
        ((scalar_id T _).app
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a))).symm _
  | succ b hab ih =>
      obtain ⟨τ, hτ, _⟩ := scalar_truncation_triangle T
        (pbcAdicQuotient T d (b + 1) b (Nat.le_succ b))
        (M.level (b + 1)) (M.level b) (M.normalization (b + 1) b (Nat.le_succ b)) m
        (hTor b)
      let τ₃ : (pbcDerivedExtend
          (pbcAdicQuotient T d (b + 1) b (Nat.le_succ b))).obj
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level (b + 1))) ≅
          (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b) :=
        (Triangle.π₃ : Triangle _ ⥤ _).mapIso τ
      let e : (pbcDerivedExtend
          (pbcAdicQuotient T d (b + 1) a (hab.trans (Nat.le_succ b)))).obj
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level (b + 1))) ≅
          (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) :=
        (pbcReductionNormalization
        (pbcAdicQuotient T d (b + 1) b (Nat.le_succ b))
        (pbcAdicQuotient T d b a hab)
        (pbcAdicQuotient T d (b + 1) a (hab.trans (Nat.le_succ b)))
        (pbcAdicQuotient_comp T d (b + 1) b a hab (Nat.le_succ b))
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level (b + 1)))).symm ≪≫
          (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso τ₃
      have := ih
      exact DerivedCategory.TStructure.t.isGE_of_iso e.symm _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem allpair_truncation_triangle (M : AdicTower T d) (m : ℤ)
    (hTor : PbcLevelwiseTorVanishing T d M m) (b a : ℕ) (hab : a ≤ b) :
    ∃! τ : (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level a),
      τ.hom.hom₂ = (M.normalization b a hab).hom := by
  let φ := pbcAdicQuotient T d b a hab
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have : (pbcDerivedScalarAdjunction φ).CommShift ℤ :=
    (pbcDerivedScalarAdjunction φ).commShift_of_rightAdjoint ℤ
  have : (pbcDerivedRestrict φ).IsTriangulated :=
    inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.IsTriangulated)
  have : (pbcDerivedExtend φ).IsTriangulated :=
    (pbcDerivedScalarAdjunction φ).isTriangulated_leftAdjoint
  have hLE : ((pbcDerivedExtend φ).obj
      ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b))).IsLE m :=
    (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u} φ m).1
      _ inferInstance
  have hGE := truncation_upper_bound T d M m hTor b a hab
  let t := DerivedCategory.TStructure.t (C := pbcModules T ((pbcAdicRings T d).obj (op a)))
  have hs := (pbcDerivedExtend φ).map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished m (m + 1) rfl (M.level b))
  have ht := t.triangleLEGE_distinguished m (m + 1) rfl (M.level a)
  obtain ⟨τ, hτ⟩ := t.triangle_iso_exists hs ht (M.normalization b a hab) m (m + 1)
    hLE hGE (by
      change t.IsLE ((t.truncLE m).obj (M.level a)) m
      infer_instance) (by
      change t.IsGE ((t.truncGE (m + 1)).obj (M.level a)) (m + 1)
      infer_instance)
  refine ⟨τ, hτ, ?_⟩
  intro σ hσ
  apply Iso.ext
  exact t.triangle_map_ext hs ht m (m + 1) hLE (by
    change t.IsGE ((t.truncGE (m + 1)).obj (M.level a)) (m + 1)
    infer_instance) (hσ.trans hτ.symm)

end ScalarBounds

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem triangle_adjuncts (M : AdicTower T d) (m : ℤ)
    (b a : ℕ) (hab : a ≤ b)
    (τ : (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level a))
    (hτ : τ.hom.hom₂ = (M.normalization b a hab).hom) :
    (pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app
          ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b)) ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map τ.hom.hom₁ =
      pbcTruncatedTransitionLE T d M m b a hab ∧
    (pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map τ.hom.hom₃ =
      pbcTruncatedTransitionGE T d M m b a hab := by
  let φ := pbcAdicQuotient T d b a hab
  let F := pbcDerivedExtend φ
  let G := pbcDerivedRestrict φ
  let adj := pbcDerivedScalarAdjunction φ
  let eLE : F.obj ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj (M.level a) :=
    (Triangle.π₁ : Triangle _ ⥤ _).mapIso τ
  let eGE : F.obj ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a) :=
    (Triangle.π₃ : Triangle _ ⥤ _).mapIso τ
  change adj.unit.app _ ≫ G.map eLE.hom = _ ∧
    adj.unit.app _ ≫ G.map eGE.hom = _
  have hLE : F.map ((DerivedCategory.TStructure.t.truncLEι m).app (M.level b)) ≫
      (M.normalization b a hab).hom =
      eLE.hom ≫ (DerivedCategory.TStructure.t.truncLEι m).app (M.level a) := by
    simpa only [Functor.mapTriangle_obj,
      CategoryTheory.Triangulated.TStructure.triangleLEGE_obj_mor₁, hτ] using! τ.hom.comm₁
  have hGE : F.map ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b)) ≫
      eGE.hom = (M.normalization b a hab).hom ≫
        (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level a) := by
    simpa only [Functor.mapTriangle_obj,
      CategoryTheory.Triangulated.TStructure.triangleLEGE_obj_mor₂, hτ] using! τ.hom.comm₂
  constructor
  · apply (cancel_mono
      (((pbcRestrict φ).mapDerivedCategoryTruncLEIso m).hom.app (M.level a))).mp
    have : DerivedCategory.TStructure.t.IsLE
        ((𝟭 (DerivedCategory _)).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b))) m := by
      dsimp
      infer_instance
    apply DerivedCategory.TStructure.t.to_truncLE_obj_ext
    have hcmp : ((pbcRestrict φ).mapDerivedCategoryTruncLEIso m).hom.app
          (M.level a) ≫
        (DerivedCategory.TStructure.t.truncLEι m).app (G.obj (M.level a)) =
        G.map ((DerivedCategory.TStructure.t.truncLEι m).app (M.level a)) :=
      truncLE_comparison_counit (pbcRestrict φ) (M.level a) m
    simp only [pbcTruncatedTransitionLE, φ, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    erw [hcmp, ← G.map_comp, ← hLE, G.map_comp]
    have hn := adj.unit.naturality
      ((DerivedCategory.TStructure.t.truncLEι m).app (M.level b))
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← Category.assoc, ← hn]
    simpa only [Functor.id_map, adicTowerSemilinearTransition, adj, G,
      Category.assoc] using!
      ((DerivedCategory.TStructure.t.truncLEι m).naturality
        (adicTowerSemilinearTransition T d M.level M.normalization b a hab)).symm
  · have : DerivedCategory.TStructure.t.IsGE
        (G.obj ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)))
        (m + 1) := (pbcRestrict φ).isGE_mapDerivedCategory_obj _ _
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
    simp only [pbcTruncatedTransitionGE]
    have hn := adj.unit.naturality
      ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b))
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    erw [← Category.assoc, hn]
    simp only [Category.assoc]
    erw [← G.map_comp, hGE, G.map_comp]
    erw [← NatTrans.naturality_assoc]
    simp only [Functor.id_map]
    erw [truncGE_restriction_unit]
    simp only [adicTowerSemilinearTransition, adj, G, Category.assoc, Functor.id_obj]
    rfl
private def truncated_evaluationLE (M : AdicTower T d) (m : ℤ) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level n)) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj M.tower) :=
  ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncLEIso m).app
      (M.level n) ≪≫
    (DerivedCategory.TStructure.t.truncLE m).mapIso (M.evaluation n) ≪≫
      (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
        (op n)).mapDerivedCategoryTruncLEIso m).symm.app M.tower

private def truncated_evaluationGE (M : AdicTower T d) (m : ℤ) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower) :=
  ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncGEIso (m + 1)).app
      (M.level n) ≪≫
    (DerivedCategory.TStructure.t.truncGE (m + 1)).mapIso (M.evaluation n) ≪≫
      (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
        (op n)).mapDerivedCategoryTruncGEIso (m + 1)).symm.app M.tower

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncated_evaluationLE_counit (M : AdicTower T d) (m : ℤ) (n : ℕ) :
    (truncated_evaluationLE T d M m n).hom ≫
        (pbcTowerEvaluation T (pbcAdicCompletion T d) n).map
          ((DerivedCategory.TStructure.t.truncLEι m).app M.tower) =
      (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n)) ≫
        (M.evaluation n).hom := by
  dsimp only [pbcDerivedRestrict, pbcTowerEvaluation, truncated_evaluationLE,
    Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc]
  erw [truncLE_restriction_counit]
  erw [(DerivedCategory.TStructure.t.truncLEι m).naturality]
  simp only [Functor.id_map]
  erw [← Category.assoc, truncLE_comparison_counit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncated_evaluationGE_unit (M : AdicTower T d) (m : ℤ) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n)) ≫
        (truncated_evaluationGE T d M m n).hom =
      (M.evaluation n).hom ≫
        (pbcTowerEvaluation T (pbcAdicCompletion T d) n).map
          ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app M.tower) := by
  dsimp only [pbcDerivedRestrict, pbcTowerEvaluation, truncated_evaluationGE,
    Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  erw [← Category.assoc, ← Category.assoc, truncGE_comparison_unit]
  erw [← NatTrans.naturality]
  simp only [Functor.id_map, Category.assoc]
  erw [truncGE_restriction_unit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncated_strict_transitionLE (M : AdicTower T d) (m : ℤ)
    (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        (pbcTruncatedTransitionLE T d M m b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab)).hom.app
          ((DerivedCategory.TStructure.t.truncLE m).obj (M.level a)) ≫
      (truncated_evaluationLE T d M m a).hom =
    (truncated_evaluationLE T d M m b).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app
        ((DerivedCategory.TStructure.t.truncLE m).obj M.tower) := by
  dsimp only [pbcDerivedRestrict, pbcTowerEvaluation]
  let E := (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op a)
  have : DerivedCategory.TStructure.t.IsLE
      (((pbcRestrict (pbcAdicProjection T d b)).mapDerivedCategory).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b))) m :=
    (pbcRestrict (pbcAdicProjection T d b)).isLE_mapDerivedCategory_obj _ _
  apply (cancel_mono ((E.mapDerivedCategoryTruncLEIso m).hom.app M.tower)).mp
  apply DerivedCategory.TStructure.t.to_truncLE_obj_ext
  simp only [Category.assoc]
  erw [truncLE_comparison_counit]
  erw [truncated_evaluationLE_counit]
  have hn := (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).naturality
    ((DerivedCategory.TStructure.t.truncLEι m).app M.tower)
  erw [← hn]
  erw [reassoc_of% truncated_evaluationLE_counit T d M m b]
  have hc := (pbcDerivedRestrictComp (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab)).hom.naturality
      ((DerivedCategory.TStructure.t.truncLEι m).app (M.level a))
  dsimp only [Functor.comp_map] at hc
  erw [← reassoc_of% hc]
  erw [← Functor.map_comp_assoc]
  erw [← ((pbc_levelwise_truncation_cohomology T d M m).2.2.2.2 b a hab).1]
  have ht := M.transition b a hab
  dsimp only [pbcDerivedRestrict] at ht
  erw [Functor.map_comp]
  simp only [Category.assoc]
  rw [ht]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncated_strict_transitionGE (M : AdicTower T d) (m : ℤ)
    (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        (pbcTruncatedTransitionGE T d M m b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab)).hom.app
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)) ≫
      (truncated_evaluationGE T d M m a).hom =
    (truncated_evaluationGE T d M m b).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower) := by
  dsimp only [pbcDerivedRestrict, pbcTowerEvaluation]
  let E := (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op a)
  have : DerivedCategory.TStructure.t.IsGE
      (E.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower)) (m + 1) :=
    E.isGE_mapDerivedCategory_obj _ _
  apply (cancel_epi (((pbcRestrict (pbcAdicProjection T d b)).mapDerivedCategoryTruncGEIso
    (m + 1)).inv.app (M.level b))).mp
  apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
  simp only [← Category.assoc]
  erw [truncGE_restriction_unit]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc]
  erw [← ((pbc_levelwise_truncation_cohomology T d M m).2.2.2.2 b a hab).2]
  erw [Functor.map_comp, Category.assoc]
  have hc := (pbcDerivedRestrictComp (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab)).hom.naturality
      ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level a))
  dsimp only [Functor.comp_map] at hc
  erw [reassoc_of% hc]
  erw [truncated_evaluationGE_unit T d M m a]
  have ht := M.transition b a hab
  dsimp only [pbcDerivedRestrict] at ht
  erw [reassoc_of% ht]
  erw [reassoc_of% truncated_evaluationGE_unit T d M m b]
  have hn := (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).naturality
    ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app M.tower)
  erw [hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncate_semilinear_compLE
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (U : D ⥤ C) (V : E ⥤ D) (W : E ⥤ C)
    [U.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (e : V.mapDerivedCategory ⋙ U.mapDerivedCategory ≅ W.mapDerivedCategory)
    {X : DerivedCategory C} {Y : DerivedCategory D} {Z : DerivedCategory E}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (g : Y ⟶ V.mapDerivedCategory.obj Z)
    (h : X ⟶ W.mapDerivedCategory.obj Z)
    (hh : h = f ≫ U.mapDerivedCategory.map g ≫ e.hom.app Z) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncLE m).map h ≫
        (W.mapDerivedCategoryTruncLEIso m).inv.app Z =
      (DerivedCategory.TStructure.t.truncLE m).map f ≫
        (U.mapDerivedCategoryTruncLEIso m).inv.app Y ≫
        U.mapDerivedCategory.map
          ((DerivedCategory.TStructure.t.truncLE m).map g ≫
            (V.mapDerivedCategoryTruncLEIso m).inv.app Z) ≫
        e.hom.app ((DerivedCategory.TStructure.t.truncLE m).obj Z) := by
  apply (cancel_mono ((W.mapDerivedCategoryTruncLEIso m).hom.app Z)).mp
  have : DerivedCategory.TStructure.t.IsLE
      ((𝟭 (DerivedCategory C)).obj ((DerivedCategory.TStructure.t.truncLE m).obj X)) m :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncLE m).obj X).IsLE m)
  apply DerivedCategory.TStructure.t.to_truncLE_obj_ext
  simp only [Category.assoc, truncLE_comparison_counit]
  rw [truncated_stepLE_counit]
  rw [← e.hom.naturality
    ((DerivedCategory.TStructure.t.truncLEι m).app Z)]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, Category.assoc, truncated_stepLE_counit V g m]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% truncated_stepLE_counit U f m]
  simp only [hh, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem truncate_semilinear_compGE
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (U : D ⥤ C) (V : E ⥤ D) (W : E ⥤ C)
    [U.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (e : V.mapDerivedCategory ⋙ U.mapDerivedCategory ≅ W.mapDerivedCategory)
    {X : DerivedCategory C} {Y : DerivedCategory D} {Z : DerivedCategory E}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (g : Y ⟶ V.mapDerivedCategory.obj Z)
    (h : X ⟶ W.mapDerivedCategory.obj Z)
    (hh : h = f ≫ U.mapDerivedCategory.map g ≫ e.hom.app Z) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGE m).map h ≫
        (W.mapDerivedCategoryTruncGEIso m).inv.app Z =
      (DerivedCategory.TStructure.t.truncGE m).map f ≫
        (U.mapDerivedCategoryTruncGEIso m).inv.app Y ≫
        U.mapDerivedCategory.map
          ((DerivedCategory.TStructure.t.truncGE m).map g ≫
            (V.mapDerivedCategoryTruncGEIso m).inv.app Z) ≫
        e.hom.app ((DerivedCategory.TStructure.t.truncGE m).obj Z) := by
  have : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE m ⋙ W.mapDerivedCategory).obj Z) m := by
    change DerivedCategory.TStructure.t.IsGE
      (W.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE m).obj Z)) m
    exact W.isGE_mapDerivedCategory_obj _ _
  apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
  rw [truncated_stepGE_unit W h m]
  rw [reassoc_of% truncated_stepGE_unit U f m]
  rw [← Functor.map_comp_assoc, truncated_stepGE_unit V g m]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality ((DerivedCategory.TStructure.t.truncGEπ m).app Z)
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [hh, Category.assoc, Functor.id_obj]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem construct_truncations (M : AdicTower T d) (m : ℤ)
    (hTor : PbcLevelwiseTorVanishing T d M m) :
    ∃ N : PbcLevelwiseTruncationData T d M m, PbcIsLevelwiseTruncation T d N := by
  let τ (b a : ℕ) (hab : a ≤ b) :=
    (allpair_truncation_triangle T d M m hTor b a hab).exists.choose
  have hτ (b a : ℕ) (hab : a ≤ b) :
      (τ b a hab).hom.hom₂ = (M.normalization b a hab).hom :=
    (allpair_truncation_triangle T d M m hTor b a hab).exists.choose_spec
  have hLE (b a : ℕ) (hab : a ≤ b) :=
    (triangle_adjuncts T d M m b a hab (τ b a hab) (hτ b a hab)).1
  have hGE (b a : ℕ) (hab : a ≤ b) :=
    (triangle_adjuncts T d M m b a hab (τ b a hab) (hτ b a hab)).2
  let L : AdicTower T d := {
    tower := (DerivedCategory.TStructure.t.truncLE m).obj M.tower
    level := fun n ↦ (DerivedCategory.TStructure.t.truncLE m).obj (M.level n)
    evaluation := truncated_evaluationLE T d M m
    normalization := fun b a hab ↦ (Triangle.π₁ : Triangle _ ⥤ _).mapIso (τ b a hab)
    transition := by
      intro b a hab
      change (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            (τ b a hab).hom.hom₁) ≫ _ = _
      erw [hLE]
      exact truncated_strict_transitionLE T d M m b a hab
    cocycle := by
      intro c b a hab hbc
      change ((pbcDerivedScalarAdjunction
        (pbcAdicQuotient T d c a (hab.trans hbc))).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c a (hab.trans hbc))).map
            (τ c a (hab.trans hbc)).hom.hom₁) =
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d c b hbc)).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map (τ c b hbc).hom.hom₁) ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app _ ≫
            (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (τ b a hab).hom.hom₁) ≫ _
      erw [hLE, hLE, hLE]
      simpa only [pbcTruncatedTransitionLE, pbcDerivedRestrict, Category.assoc] using
        truncate_semilinear_compLE
        (pbcRestrict (pbcAdicQuotient T d c b hbc))
        (pbcRestrict (pbcAdicQuotient T d b a hab))
        (pbcRestrict (pbcAdicQuotient T d c a (hab.trans hbc)))
        (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
          (pbcAdicQuotient T d b a hab) (pbcAdicQuotient T d c a (hab.trans hbc))
          (pbcAdicQuotient_comp T d c b a hab hbc))
        _ _ _ (M.cocycle c b a hab hbc) m }
  let U : AdicTower T d := {
    tower := (DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower
    level := fun n ↦ (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)
    evaluation := truncated_evaluationGE T d M m
    normalization := fun b a hab ↦ (Triangle.π₃ : Triangle _ ⥤ _).mapIso (τ b a hab)
    transition := by
      intro b a hab
      change (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            (τ b a hab).hom.hom₃) ≫ _ = _
      erw [hGE]
      exact truncated_strict_transitionGE T d M m b a hab
    cocycle := by
      intro c b a hab hbc
      change ((pbcDerivedScalarAdjunction
        (pbcAdicQuotient T d c a (hab.trans hbc))).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c a (hab.trans hbc))).map
            (τ c a (hab.trans hbc)).hom.hom₃) =
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d c b hbc)).unit.app _ ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map (τ c b hbc).hom.hom₃) ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a hab)).unit.app _ ≫
            (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map (τ b a hab).hom.hom₃) ≫ _
      erw [hGE, hGE, hGE]
      simpa only [pbcTruncatedTransitionGE, pbcDerivedRestrict, Category.assoc] using
        truncate_semilinear_compGE
        (pbcRestrict (pbcAdicQuotient T d c b hbc))
        (pbcRestrict (pbcAdicQuotient T d b a hab))
        (pbcRestrict (pbcAdicQuotient T d c a (hab.trans hbc)))
        (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
          (pbcAdicQuotient T d b a hab) (pbcAdicQuotient T d c a (hab.trans hbc))
          (pbcAdicQuotient_comp T d c b a hab hbc))
        _ _ _ (M.cocycle c b a hab hbc) (m + 1) }
  let N : PbcLevelwiseTruncationData T d M m := {
    lower := L
    upper := U
    lowerTower := rfl
    upperTower := rfl
    lowerLevel := fun _ ↦ rfl
    upperLevel := fun _ ↦ rfl
    lowerEvaluation := by
      intro n
      simp only [eqToIso_refl, Functor.mapIso_refl, Iso.trans_refl, Iso.refl_trans]
      rfl
    upperEvaluation := by
      intro n
      simp only [eqToIso_refl, Functor.mapIso_refl, Iso.trans_refl, Iso.refl_trans]
      rfl }
  refine ⟨N, ?_⟩
  intro b a hab
  refine ⟨τ b a hab, ?_, ?_⟩
  · refine ⟨?_, hτ b a hab, ?_⟩
    · change (τ b a hab).hom.hom₁ =
          ((pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
            (Iso.refl _)).hom ≫ (τ b a hab).hom.hom₁ ≫ 𝟙 _
      simp only [Functor.mapIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
    · change (τ b a hab).hom.hom₃ =
          ((pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
            (Iso.refl _)).hom ≫ (τ b a hab).hom.hom₃ ≫ 𝟙 _
      simp only [Functor.mapIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro σ hσ
    exact (allpair_truncation_triangle T d M m hTor b a hab).unique hσ.2.1 (hτ b a hab)

/-- Under (TC), both canonical levelwise truncations are normalized adic towers.
Their stored tower/level/evaluation data and unique triangle comparisons retain all
strict transition equations, natural cohomology identifications and quotient cocycles.
Source: blueprint order 1429, (1) and (3)
(blueprint: prop-weil-pbc-levelwise-truncations).

Proof: compute good truncations in the levelwise abelian tower category
(lem-weil-tower-category-levelwise-abelian). Tensor the truncation triangle by the next
quotient. The upper bound follows from ringedTensorCohomologicalBounds(a); (TC) gives
the lower bound of its upper end by part (b). Orthogonality and
lem-weil-pbc-triangle-morphism-extension give the unique triangle comparison with the
specified middle normalization. Applying this successively gives every quotient pair.
Uniqueness gives its naturality and cocycle. The scalar-extension unit is x↦x⊗1 on
K-flat representatives, hence a map of triangles. After exact scalar restriction, the
same uniqueness identifies its end maps with the truncated strict transitions. This
also identifies the cohomology maps with those of the normalized triangles. -/
theorem pbc_adic_levelwise_truncations (M : AdicTower T d) (m : ℤ)
    (_hTor : PbcLevelwiseTorVanishing T d M m) :
    ∃ N : PbcLevelwiseTruncationData T d M m, PbcIsLevelwiseTruncation T d N := by
  exact construct_truncations T d M m _hTor

open AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cover_of_sieve (X : Scheme.{u})
    (V : Sieve (⊤_ X.ProEt)) (hV : V ∈ ProEt.topology X (⊤_ X.ProEt)) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt) (f : ∀ i, U i ⟶ ⊤_ X.ProEt),
      Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X ∧ ∀ i, V (f i) := by
  let e : ProEt.mk (𝟙 X) ≅ ⊤_ X.ProEt :=
    (ProEt.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
  have h := (ProEt.topology X).pullback_stable e.hom hV
  obtain ⟨P, hP, hPV⟩ := ProEt.mem_topology_iff.mp h
  obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
  refine ⟨I, U, fun i ↦ f i ≫ e.hom, ?_, fun i ↦ hPV _ _ ⟨i⟩⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
  change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
    proetalePrecoverage X at hP
  have hw (i : I) : (f i).left = (U i).hom := by
    have hw := MorphismProperty.Over.w (f i)
    change (f i).left ≫ 𝟙 X = (U i).hom at hw
    exact (Category.comp_id _).symm.trans hw
  simpa only [hw] using hP

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_homology_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (K : DerivedCategory (pbcModules Y R)) (q : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((adicTowerPullback g R).obj K))) :
    IsZero ((proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      ((SheafOfModules.toSheaf _).obj ((DerivedCategory.homologyFunctor _ q).obj K))) := by
  let R' := (adicTowerInverseImage g).obj R
  let F := proEtaleRingModulePullback g R R' (Iso.refl _)
  let adj := proEtaleRingModuleAdjunction g R R' (Iso.refl _)
  let H := (DerivedCategory.homologyFunctor _ q).obj K
  have hz : IsZero (F.obj H) :=
    h.of_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
  let a := ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).homEquiv
    ((SheafOfModules.toSheaf _).obj H)
    ((SheafOfModules.toSheaf _).obj (F.obj H))).symm
      ((SheafOfModules.toSheaf _).map (adj.unit.app H))
  have : IsIso a := ringUnitComparison g R R' (Iso.refl _) adj H
  exact ((SheafOfModules.toSheaf _).map_isZero hz).of_iso (asIso a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_lisse_descent {X : Scheme.{u}} (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (V : Cover.{u + 1} proetalePrecoverage X)
    (h : ∀ i, IsFiniteLocallyConstant A
      ((upperStar (ModuleCat.{u + 1} A) (V.f i)).obj F)) :
    IsFiniteLocallyConstant A F := by
  choose I W g hg he using h
  refine ⟨(Σ i, I i), (fun p ↦ W p.1 p.2),
    (fun p ↦ g p.1 p.2 ≫ V.f p.1),
    Precoverage.comp_mem_coverings V.f V.mem₀ g hg, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := he i j
  exact ⟨M, hM, ⟨(upperStarComp (ModuleCat.{u + 1} A) (g i j) (V.f i)).app F ≪≫ e⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_finite {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : adicLisseConstantRing Y A ⟶ R)
    (K : DerivedCategory (pbcModules Y R)) (q : ℤ)
    (h : IsRelativelyFiniteLisseModule g A
      ((pbcRestrict ((adicTowerInverseImage g).map c)).obj
        ((DerivedCategory.homologyFunctor _ q).obj ((adicTowerPullback g R).obj K)))) :
    IsFiniteLocallyConstant A
      ((upperStar (ModuleCat.{u + 1} A) g).obj
        ((CoefficientSerre.proEtaleModuleRestriction Y A).obj
          ((pbcRestrict c).obj ((DerivedCategory.homologyFunctor _ q).obj K)))) := by
  let C := adicLisseConstantRing Y A
  let R' := (adicTowerInverseImage g).obj R
  let C' := (adicTowerInverseImage g).obj C
  let FR := proEtaleRingModulePullback g R R' (Iso.refl _)
  let FC := proEtaleRingModulePullback g C C' (Iso.refl _)
  let H := (DerivedCategory.homologyFunctor _ q).obj K
  let U := pbcRestrict ((adicTowerInverseImage g).map c)
  let U₀ := pbcRestrict c
  let e₁ : U.obj ((DerivedCategory.homologyFunctor _ q).obj
      ((adicTowerPullback g R).obj K)) ≅ U.obj (FR.obj H) :=
    U.mapIso ((FR.mapDerivedCategoryHomologyFunctorIso q).app K).symm
  let e₂ : FC.obj (U₀.obj H) ≅ U.obj (FR.obj H) :=
    by
    let t := proEtaleRingRestrictionPullbackInv g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    have : IsIso t := proEtaleRingRestrictionPullbackInv_isIso g C R C' R' c
      ((adicTowerInverseImage g).map c) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
    exact asIso (t.app H)
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl C')).choose
  let e₃ : FC.obj (U₀.obj H) ≅
      (proEtaleModuleInverseImage g C).obj (U₀.obj H) := by
    exact θ _
  have hf := (CoefficientSerre.relative_finite_iff g A _).mp h
  exact isFiniteLocallyConstant_of_iso
    ((CoefficientSerre.relativeRestriction g A).mapIso (e₁ ≪≫ e₂.symm ≪≫ e₃) ≪≫
      CoefficientSerre.relativePullbackComparison g A (U₀.obj H)) hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem uniform_constructible (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower T d) (a b : ℤ)
    (S : Stratification T)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel d ((V i).f j ≫ S.immersion i) M a b) :
    ∀ n q, IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient d n)
      ((pbcRestrict (pbcLevelConstantComparison T d n).hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) := by
  intro n q
  let A' := PbcQuotient d n
  let H := (DerivedCategory.homologyFunctor _ q).obj (M.level n)
  let c := (pbcLevelConstantComparison T d n).hom
  let F := (CoefficientSerre.proEtaleModuleRestriction T A').obj ((pbcRestrict c).obj H)
  apply (CoefficientSerre.coefficient_constructible_iff T A' _).mpr
  refine ⟨S, fun i ↦ finite_lisse_descent A' _ (V i) (fun j ↦ ?_)⟩
  let g := (V i).f j ≫ S.immersion i
  have hlocal : IsFiniteLocallyConstant A'
      ((upperStar (ModuleCat.{u + 1} A') g).obj F) := by
    apply local_finite g A' _ c (M.level n) q
    apply (CoefficientSerre.relative_finite_iff g A' _).mpr
    let U := pbcRestrict ((adicTowerInverseImage g).map c)
    let e := U.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((L i j).identification n))
    exact isFiniteLocallyConstant_of_iso
      ((CoefficientSerre.relativeRestriction g A').mapIso e).symm
      ((CoefficientSerre.relative_finite_iff g A' _).mp ((L i j).finiteLisse n q))
  exact isFiniteLocallyConstant_of_iso
    ((upperStarComp (ModuleCat.{u + 1} A') ((V i).f j) (S.immersion i)).app F) hlocal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constructible_iso
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    {F G : pbcModules X (adicLisseConstantRing X B)} (e : F ≅ G)
    (h : IsConstructibleProEtaleCoefficientModuleSheaf X B F) :
    IsConstructibleProEtaleCoefficientModuleSheaf X B G := by
  apply (CoefficientSerre.coefficient_constructible_iff X B G).mpr
  exact isConstructible_of_iso ((CoefficientSerre.proEtaleModuleRestriction X B).mapIso e)
    ((CoefficientSerre.coefficient_constructible_iff X B F).mp h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constructible_zero_of_constructible
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (F G : pbcModules X (adicLisseConstantRing X B))
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf X B F) (hG : IsZero G) :
    IsConstructibleProEtaleCoefficientModuleSheaf X B G := by
  have hk := ((constructibleCoefficient_exactClosure X B).1 F F (𝟙 F) hF hF).1
  exact constructible_iso X B
    ((isZero_kernel_of_mono (𝟙 F)).isoZero ≪≫ hG.isoZero.symm) hk

section LocalModelBounds
attribute [local semireducible] completedAdicDerivedChange

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem uniform_model_bounds (X : Scheme.{u}) [IsNoetherian X]
    {B : Type (u + 1)} [CommRing B] (c : AdicCoefficientDatum B)
    (M : AdicTower X c) (a b : ℤ) (S : Stratification X)
    (V : ∀ i : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain i))
    (L : ∀ (i : Fin S.n) (j : (V i).I₀),
      AdicTowerLocalModel c ((V i).f j ≫ S.immersion i) M a b)
    (hlower : ∀ i j n,
      (adicTowerLocalReduction c ((V i).f j ≫ S.immersion i) (L i j).complex n).IsGE
        (a - 1)) :
    ∀ n q, (q < a - 1 ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n)) := by
  intro n q hq
  let H := (DerivedCategory.homologyFunctor _ q).obj (M.level n)
  have hz : IsZero ((SheafOfModules.toSheaf _).obj H) := by
    apply proEtale_isZero_of_stratum_cover X S V
    intro i j
    let g := (V i).f j ≫ S.immersion i
    let P := (L i j).complex
    have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff _ _).2
      (fun q hq ↦ (L i j).bounded q (Or.inr hq))
    have hb : (adicTowerLocalReduction c g P n).IsLE b :=
      (SheafOfModules.ringedTensorCohomologicalBounds.{u + 2, u + 1, u + 1, u}
        ((adicTowerInverseImage g).map (pbcAdicProjection X c n)) b).1
          (DerivedCategory.Q.obj P) inferInstance
    have ha : (adicTowerLocalReduction c g P n).IsGE (a - 1) := hlower i j n
    have hlocal : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (adicTowerLocalReduction c g P n)) := by
      rcases hq with hq | hq
      · exact DerivedCategory.isZero_of_isGE _ (a - 1) q hq
      · exact DerivedCategory.isZero_of_isLE _ b q hq
    apply pullback_homology_zero g _ (M.level n) q
    exact hlocal.of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso ((L i j).identification n))
  apply (IsZero.iff_id_eq_zero H).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 H))
    ((SheafOfModules.toSheaf _).map (0 : H ⟶ H))

end LocalModelBounds

section PrincipalReductionProof
attribute [local semireducible] completedReductionCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end PrincipalReductionProof

section ResidueCounterexampleProof
attribute [local semireducible] completedReductionCoefficient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end ResidueCounterexampleProof

attribute [local semireducible] completedReductionCoefficient in
/-- Uniform bounded constructibility is preserved under (TC), for any coefficient datum whose
ideal is generated by a nonzero element of a domain.
Source: blueprint order 1429, (2); Stacks Tags 09C1, 09C7 and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: as for `pbc_levelwise_truncations_constructible`; the only coefficient input is the
one-degree loss of reduction by the principal two-term resolution. -/
theorem pbc_levelwise_truncations_constructible_of_principal [IsNoetherian T] [IsDomain A]
    (π : A) (hI : d.ideal = Ideal.span {π}) (hπ : π ≠ 0)
    (K : PbcCompletedDerived T d) (m d₀ d₁ : ℤ)
    (N : PbcLevelwiseTruncationData T d
      (pbcReductionAdicTower T d K) m)
    (_hN : PbcIsLevelwiseTruncation T d N)
    (_hTor : PbcLevelwiseTorVanishing T d
      (pbcReductionAdicTower T d K) m)
    (_hmodels : d₀ ≤ d₁ ∧ ∃ S : Stratification T,
      ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
        V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
        ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
          Nonempty (AdicTowerLocalModel d
            (U.hom ≫ S.immersion α)
            (pbcReductionAdicTower T d K) d₀ d₁)) :
    IsUniformlyBoundedConstructibleAdicTower d N.lower ∧
    IsUniformlyBoundedConstructibleAdicTower d N.upper ∧
    (∀ (n : ℕ) (q : ℤ), (q < d₀ - 1 ∨ min m d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) ∧
    (∀ (n : ℕ) (q : ℤ), (q < max (m + 1) (d₀ - 1) ∨ d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n))) := by
  classical
  let c := d
  let M := pbcReductionAdicTower T c K
  obtain ⟨hab, S, hS⟩ := _hmodels
  choose W hW hL using hS
  have hcov := fun i ↦ cover_of_sieve (S.domain i) (W i) (hW i)
  choose I U f hU hf using hcov
  let V (i : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain i) :=
    { I₀ := I i, X := fun j ↦ (U i j).left, f := fun j ↦ (U i j).hom, mem₀ := hU i }
  have hmodels (i : Fin S.n) (j : (V i).I₀) :
      Nonempty (AdicTowerLocalModel c ((V i).f j ≫ S.immersion i) M d₀ d₁) :=
    hL i (U i j) (f i j) (hf i j)
  let L (i : Fin S.n) (j : (V i).I₀) := Classical.choice (hmodels i j)
  have hc := uniform_constructible T c M d₀ d₁ S V L
  have hb := uniform_model_bounds T c M d₀ d₁ S V L (by
    intro i j n
    have : (L i j).complex.IsStrictlyGE d₀ :=
      (CochainComplex.isStrictlyGE_iff _ _).2
        (fun q hq ↦ (L i j).bounded q (Or.inl hq))
    exact integralLocalReduction_isGE_of_principal d π hI hπ _ _ d₀ n)
  have hminus (n : ℕ) (q : ℤ) (hq : q < d₀ - 1 ∨ min m d₁ < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n)) := by
    rw [N.lowerLevel n]
    by_cases hqm : q ≤ m
    · have hq' : q < d₀ - 1 ∨ d₁ < q := by omega
      have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (m + 1) q (by omega)
      exact (hb n q hq').of_iso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n))))
    · exact DerivedCategory.isZero_of_isLE _ m q (by omega)
  have hplus (n : ℕ) (q : ℤ)
      (hq : q < max (m + 1) (d₀ - 1) ∨ d₁ < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n)) := by
    rw [N.upperLevel n]
    by_cases hqm : m + 1 ≤ q
    · have hq' : q < d₀ - 1 ∨ d₁ < q := by omega
      have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ (m + 1) q hqm
      exact (hb n q hq').of_iso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n)))).symm
    · exact DerivedCategory.isZero_of_isGE _ (m + 1) q (by omega)
  have hcminus (n : ℕ) (q : ℤ) :
      IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient c n)
        ((pbcRestrict (pbcLevelConstantComparison T c n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) := by
    let R := pbcRestrict (pbcLevelConstantComparison T c n).hom
    rw [N.lowerLevel n]
    by_cases hqm : q ≤ m
    · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (m + 1) q (by omega)
      exact constructible_iso T _ (R.mapIso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n)))).symm) (hc n q)
    · exact constructible_zero_of_constructible T _ _ _ (hc n q)
        (R.map_isZero (DerivedCategory.isZero_of_isLE _ m q (by omega)))
  have hcplus (n : ℕ) (q : ℤ) :
      IsConstructibleProEtaleCoefficientModuleSheaf T (PbcQuotient c n)
        ((pbcRestrict (pbcLevelConstantComparison T c n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n))) := by
    let R := pbcRestrict (pbcLevelConstantComparison T c n).hom
    rw [N.upperLevel n]
    by_cases hqm : m + 1 ≤ q
    · have : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ (m + 1) q hqm
      exact constructible_iso T _ (R.mapIso
        (asIso ((DerivedCategory.homologyFunctor _ q).map
          ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n))))) (hc n q)
    · exact constructible_zero_of_constructible T _ _ _ (hc n q)
        (R.map_isZero (DerivedCategory.isZero_of_isGE _ (m + 1) q (by omega)))
  refine ⟨?_, ?_, hminus, hplus⟩
  · apply (normalizedConstructibleTower_local_effectivity T c N.lower hcminus
      (d₀ - 1) d₁ (by omega) ?_).2
    intro n q hq
    exact hminus n q (by omega)
  · apply (normalizedConstructibleTower_local_effectivity T c N.upper hcplus
      (d₀ - 1) d₁ (by omega) ?_).2
    intro n q hq
    exact hplus n q (by omega)


section IntegralCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local semireducible] completedReductionCoefficient in
/-- Uniform bounded constructibility is preserved under (TC), with the stated sharp
cohomological windows. The conclusion uses the full common-local-model predicate;
it does not claim that the original model truncations have finite free terms.
Source: blueprint order 1429, (2); Stacks Tags 09C1, 09C7 and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: pull the two-term completed quotient resolution back to each common model domain,
retaining the actual inverse-image completed ring. A model in [d0,d1] reduces into
[d0-1,d1]. Exact restriction and stratum-cover zero detection make these bounds global.
Canonical truncation intersects this interval with its surviving
range. Its cohomology remains intrinsically constructible. Under (TC) the preceding
normalization theorem supplies adic towers. Apply normalizedConstructibleTower_local_effectivity
to their constructible cohomology and common finite bounds to obtain new finite
stratifications and bounded common adic-lisse finite-type models, with compatible
reductions. This is existence of models; no assertion about a raw cone's term support
or local freeness of kernels is used. Empty surviving intervals mean zero. -/
theorem pbc_levelwise_truncations_constructible [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m d₀ d₁ : ℤ)
    (N : PbcLevelwiseTruncationData T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hN : PbcIsLevelwiseTruncation T (pbcIntegralDatum l E) N)
    (_hTor : PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hmodels : d₀ ≤ d₁ ∧ ∃ S : Stratification T,
      ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
        V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
        ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
          Nonempty (AdicTowerLocalModel (pbcIntegralDatum l E)
            (U.hom ≫ S.immersion α)
            (pbcReductionAdicTower T (pbcIntegralDatum l E) K) d₀ d₁)) :
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.lower ∧
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.upper ∧
    (∀ (n : ℕ) (q : ℤ), (q < d₀ - 1 ∨ min m d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) ∧
    (∀ (n : ℕ) (q : ℤ), (q < max (m + 1) (d₀ - 1) ∨ d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n))) := by
  let e : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E := ULift.ringEquiv
  let : IsDomain (PbcIntegralRing l E) := e.toMulEquiv.isDomain _
  have hπ : pbcUniformizer l E ≠ 0 := by
    intro h
    exact Padic.coefficientExtensionUniformizer_ne_zero l E (congrArg ULift.down h)
  exact pbc_levelwise_truncations_constructible_of_principal T (pbcIntegralDatum l E)
    (pbcUniformizer l E) rfl hπ K m d₀ d₁ N _hN _hTor _hmodels

end IntegralCoefficients

open AlgebraicGeometry.ProEtale

section OriginNormalizationProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end OriginNormalizationProof

end AlgebraicGeometry.Scheme
