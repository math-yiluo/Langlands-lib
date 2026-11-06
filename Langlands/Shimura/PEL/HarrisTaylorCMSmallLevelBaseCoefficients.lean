import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology
import Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients

/-! # Base-sheaf coefficients on the actual small geometric CM tower -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel
open Langlands.Geometry.EtaleDerivedSections

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
  (q : CMRepresentabilityStatement D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor)

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "small" => D.rationalInvolution.LevelSufficientlySmall
local notation "G" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ


local notation "geometricOver" => cmGeometricOverTower D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q
local notation "geometricBase" => Spec (CommRingCat.of (AlgebraicClosure F))

/-- The actual geometric CM structure maps, with naturality for every transporter. -/
def cmSmallLevelGeometricStructure :
    geometricSchemes ⟶ (Functor.const (SmallCMLevel D)).obj geometricBase where
  app U := ((geometricOver).obj U).hom
  naturality {U V} k := by
    change ((geometricOver).map k).left ≫ ((geometricOver).obj V).hom =
      ((geometricOver).obj U).hom ≫ 𝟙 _
    simp

local notation "structureMap" => cmSmallLevelGeometricStructure D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

/-- The coefficient base map is the original geometric-over structure map. -/
@[simp] theorem cmSmallLevelGeometricStructure_app (U : SmallCMLevel D) :
    (structureMap).app U = ((geometricOver).obj U).hom := rfl

/-- The structure maps commute with the original geometric transporter. -/
theorem cmSmallLevelGeometricStructure_naturality {U V : SmallCMLevel D} (k : U ⟶ V) :
    (geometricSchemes).map k ≫ (structureMap).app V = (structureMap).app U := by
  simpa using (structureMap).naturality k

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion
local notation "selfTrivial" => cmGeometricSchemeTower_restrictedSelfArrow D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q

variable (R : Type) [CommRing R]

local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R
local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

/-- The coefficient at each actual CM level is inverse image of the given base sheaf.
The compatible transition maps are constructed inverse-image comparisons. -/
def cmSmallLevelBaseCoefficients (M : ModuleSheaf geometricBase R) : coefficients := by
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.canonicalCoefficients R structureMap M

local notation "baseCoefficients" => cmSmallLevelBaseCoefficients D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

/-- The coefficients are the genuine inverse images along the actual structure map. -/
@[simp] theorem cmSmallLevelBaseCoefficients_obj (M : ModuleSheaf geometricBase R)
    (U : SmallCMLevel D) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (baseCoefficients M).obj (op U) =
      (EtaleInverseImage.inverseImage ((structureMap).app U) R).obj M := rfl

/-- Each coefficient transition is the projection comparison for the same transporter. -/
theorem cmSmallLevelBaseCoefficients_map (M : ModuleSheaf geometricBase R)
    {U V : SmallCMLevel D} (k : U ⟶ V) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (baseCoefficients M).map k.op =
      (LevelTowerCohomology.restrictionProjectionIso R
        ((structureMap).app V) ((structureMap).app U) ((geometricSchemes).map k)
        (cmSmallLevelGeometricStructure_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q k)).hom.app M := by
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  rfl

/-- For these constructed coefficients, scheme self-arrow triviality proves the full
sheaf-level identity; no extra coefficient-triviality premise is assumed. -/
theorem cmSmallLevelBaseCoefficients_trivial (M : ModuleSheaf geometricBase R) :
    trivialCoefficients (baseCoefficients M) := by
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.isLevelTrivialCoefficients_canonical R selfTrivial M

/-- Base sheaves map functorially into the actual level-trivial CM coefficient diagrams. -/
def cmSmallLevelBaseCoefficientsFunctor :
    ModuleSheaf geometricBase R ⥤ (trivialCoefficients).FullSubcategory := by
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.levelTrivialCanonicalCoefficientsFunctor
    R structureMap selfTrivial

local notation "baseCoefficientFunctor" => cmSmallLevelBaseCoefficientsFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

@[simp] theorem cmSmallLevelBaseCoefficientsFunctor_obj (M : ModuleSheaf geometricBase R) :
    ((baseCoefficientFunctor).obj M).obj = baseCoefficients M := rfl

/-- A base-sheaf morphism induces its actual inverse-image morphism at every level. -/
@[simp] theorem cmSmallLevelBaseCoefficientsFunctor_map_app
    {M N : ModuleSheaf geometricBase R} (α : M ⟶ N) (U : SmallCMLevel D) :
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (((baseCoefficientFunctor).map α).hom).app (op U) =
      (EtaleInverseImage.inverseImage ((structureMap).app U) R).map α := rfl

/-- The cohomology object is ordinary small-etale cohomology of the actual level scheme. -/
theorem cmSmallLevelBaseCoefficients_cohomology_obj (M : ModuleSheaf geometricBase R)
    (d : ℕ) (U : SmallCMLevel D) :
    (cmSmallLevelCohomology D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R (baseCoefficients M) d).obj (op U) =
      (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) R d).obj
        ((EtaleInverseImage.inverseImage ((structureMap).app U) R).obj M) := rfl

/-- The smooth finite-adelic action on shrinking-level cohomology of actual base coefficients. -/
def cmSmallLevelBaseCohomologyFunctor (d : ℕ) :
    ModuleSheaf geometricBase R ⥤ SmoothRep.{0, 0, 0} R G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalCohomologyFunctor
    R structureMap selfTrivial d

local notation "baseCohomologyFunctor" => cmSmallLevelBaseCohomologyFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R

/-- This functor uses exactly the previously constructed actual CM smooth colimit. -/
@[simp] theorem cmSmallLevelBaseCohomologyFunctor_obj (d : ℕ)
    (M : ModuleSheaf geometricBase R) :
    (baseCohomologyFunctor d).obj M =
      cmSmallLevelSmoothCohomology D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R (baseCoefficients M)
        (cmSmallLevelBaseCoefficients_trivial D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R M) d := rfl

/-- Shrinking-level global sections of the same actual inverse-image coefficients. -/
def cmSmallLevelBaseSectionsFunctor :
    ModuleSheaf geometricBase R ⥤ SmoothRep.{0, 0, 0} R G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalSectionsFunctor
    R structureMap selfTrivial

/-- Degree-zero cohomology agrees naturally with actual shrinking-level sections. -/
def cmSmallLevelBaseCohomologyZeroIso :
    baseCohomologyFunctor 0 ≅ cmSmallLevelBaseSectionsFunctor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q existence geometry hRigid criterion R := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalCohomologyZeroIso
    R structureMap selfTrivial

/-- Translation pulls a class back along the original geometric transporter to the
conjugate level and uses its constructed projection-coefficient comparison. -/
theorem cmSmallLevelBaseCohomology_action (d : ℕ) (M : ModuleSheaf geometricBase R)
    (g : G) (U : SmallCMLevel D)
    (x : (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) R d).obj
      ((EtaleInverseImage.inverseImage ((structureMap).app U) R).obj M)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    ((baseCohomologyFunctor d).obj M).obj.ρ g
        ((RestrictedLevelColimit.ι ((baseCoefficients M).cohomology d) U).hom x) =
      (RestrictedLevelColimit.ι ((baseCoefficients M).cohomology d)
        (restrictedConj small g U)).hom
        ((cohomologyMapWithCoefficients
          ((geometricSchemes).map (restrictedConjArrow small g U)) R d
          ((baseCoefficients M).map (restrictedConjArrow small g U).op)).hom x) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothCanonicalCohomology_ρ_ι_apply
    R structureMap selfTrivial d M g U x

/-- Every class is represented at one actual small CM level, provided one exists. -/
theorem cmSmallLevelBaseCohomology_exists_level [Nonempty (SmallCMLevel D)]
    (d : ℕ) (M : ModuleSheaf geometricBase R)
    (x : ((baseCohomologyFunctor d).obj M).obj.V) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    ∃ (U : SmallCMLevel D)
      (y : (EtaleDerivedSections.cohomology ((geometricSchemes).obj U) R d).obj
        ((EtaleInverseImage.inverseImage ((structureMap).app U) R).obj M)),
      (RestrictedLevelColimit.ι ((baseCoefficients M).cohomology d) U).hom y = x := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.canonicalCohomology_exists_level
    R structureMap selfTrivial d M x

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
