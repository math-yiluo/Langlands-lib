import Langlands.Cohomology.AbelianScheme.PowerQuasiIsogenyPullback
import Langlands.Shimura.PEL.HarrisTaylorCMUniversalTransport
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientProjectorStatement
import Langlands.Shimura.PEL.HarrisTaylorCMLambdaTower
import Langlands.Shimura.PEL.HarrisTaylorCMNormalRefinement

/-! # Transport of the geometric coefficient realization along CM level maps -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe wS wR wGeo wPadic

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme Langlands.Shimura
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
open Langlands.Global AdelicFunctoriality
open Langlands.Global.CompletionPadic (residuePrime)
open Langlands.GaloisRepresentation (absoluteCyclotomicCharacter)
open Langlands.Cohomology.AbelianPower
open Langlands.Shimura.CompactOpenLevel Langlands.Shimura.LevelHecke

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.FiniteEtale

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)
  (lam : FinitePlacesAbove K p)

local notation "Klam" => FiniteCompletion K lam.1
local notation "Λ" => AlgebraicClosure Klam
local notation "ell" => residuePrime lam.1
local notation "reps" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "baseTower" => representedCMBaseTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor reps

private abbrev levelComponents (U : SmallCMLevel D) :=
  _root_.ConnectedComponents (reps U).base.obj.left

local notation "Component" U:max => levelComponents D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U
local notation "baseComponent" U:max c:max => componentCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality (reps U).base c
local notation "family" U:max c:max => cmUniversalAbelianFamily D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor (reps U) c
local notation "imageComponent" b:max c:max => componentMap ((baseTower).map b).hom.left c
local notation "componentArrow" b:max c:max => componentCMBaseHomTo D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  ((baseTower).map b) c (imageComponent b c) rfl
local notation "path" b:max c:max => cmUniversalLevelPathChoice D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor reps b c
local notation "transport" b:max c:max => cmUniversalLevelTransport D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor reps b c (path b c)

private abbrev projectorCoefficientExtension : ℚ_[ell] →+* Λ :=
  (algebraMap Klam Λ).comp (Langlands.Global.CompletionPadic.padicMap lam.1)

local notation "j" => projectorCoefficientExtension p lam

variable [geomDerived : ∀ X : Scheme.{0}, HasDerivedCategory.{wGeo}
    (EtaleDerivedSections.ModuleSheaf X ℤ_[residuePrime lam.1])]
  [padicDerived : HasDerivedCategory.{wPadic} (ModuleCat ℤ_[residuePrime lam.1])]
  [∀ U : SmallCMLevel D, HasDerivedCategory.{wS}
    (EtaleDerivedSections.ModuleSheaf ((cmGeometricSchemeTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q).obj U)
        (HarrisCoefficientIntegers K p))]
  [HasDerivedCategory.{wR} (ModuleCat.{0} (HarrisCoefficientIntegers K p))]

set_option hygiene false in
local notation "powerCohom" U:max c:max m:max i:max =>
  cohomologyAction.{wGeo, wPadic} (family U c) (baseComponent U c).obj.hom m ell j i

/-- Pullback on the projected cohomology uses the actual cleared power map and
compensates the polarization multiplier on the Tate line. -/
def cmProjectorLevelPullback {U V : SmallCMLevel D} (b : U ⟶ V) (c : Component U)
    (m t degree : ℕ) :
    (powerCohom V (imageComponent b c) m degree).V →ₗ[Λ] (powerCohom U c m degree).V :=
  let a := transport b c
  letI := auxiliaryStarRing D C
  (((a.multiplier : ℚ) : Λ) ^ t)⁻¹ •
    quasiIsogenyPullback.{wGeo, wPadic} (componentArrow b c).hom.left (Over.w (componentArrow b c).hom)
      m ell j (RationalAlgebraAction.underlyingIso a.iso) degree

private abbrev extendedLevelCohomology (i : ℕ) :=
  cmHarrisLambdaLevelCohomology.{wS, wR} D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p ρ existence geometry hRigid lam i ⋙
      LatticeGaloisRepresentation.baseChangeActionFunctor (L := Λ)

private abbrev levelProjector (U : SmallCMLevel D) (c : Component U) {m : ℕ}
    (e : FreeAlgebra Λ (GeometricOperator A m)) (i : ℕ) :=
  projectedPELAction.{wGeo, wPadic} (family U c) (baseComponent U c).obj.hom m ell j
    (cmProjectorPEL D C preservation composition unitCoherence associativity comparison symmetry
      stability square universality dualityNaturality polarizationStability compatibility h htor q U c)
    (2 * Module.finrank ℚ E * n^2) i e

private abbrev levelTateScalar (t : ℕ) (σ : Field.absoluteGaloisGroup F) : Λ :=
  ((j).comp (PadicInt.Coe.ringHom (p := ell))) ((absoluteCyclotomicCharacter ell F σ).val ^ t)

set_option hygiene false in
local notation "H" i:max => extendedLevelCohomology.{wS, wR} D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor q ρ p existence geometry hRigid lam i

set_option hygiene false in
local notation "P" U:max c:max e:max i:max =>
  levelProjector.{wGeo, wPadic} D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability compatibility
    h htor q p lam U c e i

set_option hygiene false in
local notation "fixedComparison" i:max =>
  CMHarrisLambdaTowerFixedVectorComparison.{wS, wR} D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p ρ existence geometry hRigid lam i

set_option hygiene false in
local notation "towerOverClosure" i:max =>
  cmHarrisLambdaTowerExtendScalars.{wS, wR} D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p ρ existence geometry hRigid lam i Λ

set_option hygiene false in
local notation "fixedIso" i:max hfix:max U:max =>
  cmHarrisLambdaTowerExtendScalarsFixedVectorsIso.{wS, wR} D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p ρ existence geometry hRigid lam i Λ hfix U

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

/-- The actual double-coset operator transported back to coefficient cohomology
at the two specified small levels. -/
def cmProjectorHeckeOperator (i : ℕ) (hfix : fixedComparison i) (U V : SmallCMLevel D)
    (g : OriginalGroup) : ((H i).obj (op V)).V →ₗ[Λ] ((H i).obj (op U)).V :=
  ((fixedIso i hfix U).inv.hom.hom).comp
    ((heckeOperator (towerOverClosure i).V.representation
      (inverseOpposite U.obj) (inverseOpposite V.obj) (MulOpposite.unop g)⁻¹).comp
        (fixedIso i hfix V).hom.hom.hom)

set_option hygiene false in
local notation "powerPull" b:max c:max m:max t:max i:max =>
  cmProjectorLevelPullback.{wGeo, wPadic} D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q p lam b c m t i

private abbrev normalLevelTransfer (i : ℕ) :=
  ∀ (U V : SmallCMLevel D) (_ : V.obj.subgroup ≤ U.obj.subgroup)
    [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal],
    ((H i).obj (op V)).V →ₗ[Λ] ((H i).obj (op U)).V

set_option hygiene false in
local notation "Transfer" i:max =>
  normalLevelTransfer.{wS, wR} D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor q ρ p existence geometry hRigid lam i

private def normalTraceEquations (m t : ℕ) (e : FreeAlgebra Λ (GeometricOperator A m)) (i : ℕ)
    (Φ : ∀ U : SmallCMLevel D, ((H i).obj (op U)).V ≃ₗ[Λ]
      (∀ c : Component U, (P U c e (i + m)).range))
    (trace : Transfer i) : Prop :=
  ∀ (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
    [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal],
    letI : Fintype (SmallCMResidualGroup D U V) :=
      @Fintype.ofFinite _ (smallCMResidualGroup_finite D U V)
    let b := smallCMInclusion D hVU
    let deck (g : SmallCMResidualGroup D U V) := smallCMNormalInverseArrow D U V hVU g.out
    let pull := ((H i).map b.op).hom.hom
    Function.Injective pull ∧
    ∀ x : ((H i).obj (op V)).V,
      pull (trace U V hVU x) =
        (∑ g : SmallCMResidualGroup D U V, ((H i).map (deck g).op).hom.hom x) ∧
      ∀ c : Component V,
        (powerPull b c m t (i + m)) (Φ U (trace U V hVU x) (imageComponent b c)).val =
          ∑ g : SmallCMResidualGroup D U V,
            (powerPull (deck g) c m t (i + m)) (Φ V x (imageComponent (deck g) c)).val

private def heckeTraceEquation (i : ℕ) (hfix : fixedComparison i)
    (trace : Transfer i) : Prop :=
  ∀ (U V : SmallCMLevel D) (g : OriginalGroup) (N : SmallCMLevel D),
    let M := smallCMHeckeLevel D U V g
    ∀ (hNM : N.obj.subgroup ≤ M.obj.subgroup) (hNU : N.obj.subgroup ≤ U.obj.subgroup)
      [(N.obj.subgroup.subgroupOf U.obj.subgroup).Normal],
      let b := smallCMInclusion D hNM ≫ smallCMHeckeRight D U V g
      ∀ x : ((H i).obj (op V)).V,
        cmProjectorHeckeOperator.{wS, wR} D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q ρ p existence geometry hRigid lam
          i hfix U V g x =
            ((Nat.card (SmallCMResidualGroup D M N) : Λ)⁻¹) •
              trace U N hNU (((H i).map b.op).hom.hom x)

/-- One geometric coefficient realization for all represented small levels, with
Galois equivariance, naturality for every original transporter and the normal
refinement formula for the double-coset operator. -/
def HarrisCMGeometricCoefficientLevelComparisonStatement (w : ℤ) : Prop :=
  (∀ a : A, a ≠ 0 → IsUnit a) →
  Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (ρ.act (AlgebraicClosure K))) →
  (∀ (g : (D.rationalInvolution.baseChange K).similitudes) (u : Kˣ),
    ((g.1.1 : K ⊗[ℚ] A) = algebraMap K (K ⊗[ℚ] A) u) →
      ∀ x : W, ρ.rationalAction g x = ((u : K) ^ (-w)) • x) →
  ∃ (m t : ℕ) (e : FreeAlgebra Λ (GeometricOperator A m)),
    2 * (t : ℤ) - (m : ℤ) = w ∧
    (∀ (U : SmallCMLevel D) (c : Component U) (degree : ℕ),
      IsIdempotentElem (P U c e degree)) ∧
    ∀ i : ℕ,
      ∃ Φ : ∀ U : SmallCMLevel D,
        ((H i).obj (op U)).V ≃ₗ[Λ] (∀ c : Component U, (P U c e (i + m)).range),
        (∀ (U : SmallCMLevel D) (σ : Field.absoluteGaloisGroup F)
          (x : ((H i).obj (op U)).V) (c : Component U),
          (Φ U ((((H i).obj (op U)).ρ σ).asHom.hom x) c).val =
            levelTateScalar (F := F) p lam t σ •
              ((powerCohom U c m (i + m)).ρ σ).asHom.hom (Φ U x c).val) ∧
        (∀ {U V : SmallCMLevel D} (b : U ⟶ V) (x : ((H i).obj (op V)).V) (c : Component U),
          (Φ U (((H i).map b.op).hom.hom x) c).val =
            (powerPull b c m t (i + m)) (Φ V x (imageComponent b c)).val) ∧
        ∀ hfix : fixedComparison i, ∃ trace : Transfer i,
          normalTraceEquations.{wS, wR, wGeo, wPadic} D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q ρ p existence geometry hRigid lam
            m t e i Φ trace ∧
          heckeTraceEquation.{wS, wR} D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality polarizationStability
            compatibility h htor q ρ p existence geometry hRigid lam i hfix trace

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
