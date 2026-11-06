import Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelIndex
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricTransporterEtale
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLevelCosets
import Langlands.Shimura.RestrictedLevelTowerCohomology

/-! # Shrinking-level cohomology of the actual geometric CM tower -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.AlgebraInvolution

variable {B : Type u} [Ring B] [Algebra ℚ B] (σ : AlgebraInvolution ℚ B)

/-- The actual ordered small-level index is the restricted ordered index. -/
theorem orderedSmallLevel_eq_restrictedOrdered :
    σ.OrderedSmallLevel = CompactOpenLevel.RestrictedOrdered σ.LevelSufficientlySmall := rfl

/-- The actual inclusion functor is precisely the generic restricted inclusion. -/
theorem orderedSmallLevelToSmallLevelCategory_eq_restrictedInclusion :
    σ.orderedSmallLevelToSmallLevelCategory =
      CompactOpenLevel.restrictedInclusion σ.LevelSufficientlySmall := rfl

/-- The ordered forgetful functor is the same restricted forgetful functor. -/
theorem orderedSmallLevelForget_eq_restrictedForget :
    σ.orderedSmallLevelForget =
      CompactOpenLevel.restrictedForget σ.LevelSufficientlySmall := rfl

variable [Module.Finite ℚ B]

/-- Sufficient smallness of the actual adelic group passes to smaller levels. -/
instance sufficientlySmall_isDownwardClosed :
    CompactOpenLevel.IsDownwardClosed σ.LevelSufficientlySmall where
  of_le hKL hL := hL.mono hKL

/-- Sufficient smallness is stable under the conjugation used by colimit actions. -/
instance sufficientlySmall_isConjStable :
    CompactOpenLevel.IsConjStable σ.LevelSufficientlySmall where
  conjLevel g {_} hK := hK.conjLevel σ g

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Geometry Langlands.Geometry.EtalePullback
open CompactOpenLevel

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

/-- The subgroup self-arrow fixes the actual geometric scheme at that same level.
This does not assert an identity on a general coefficient sheaf. -/
theorem cmGeometricSchemeTower_restrictedSelfArrow (U : SmallCMLevel D)
    (k : G) (hk : k ∈ U.obj.subgroup) :
    (geometricSchemes).map (restrictedSelfArrow small U k hk) = 𝟙 _ :=
  cmGeometricSchemeTower_map_eq_id_of_mem D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q (restrictedSelfArrow small U k hk) hk

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

include existence geometry hRigid criterion

/-- Every arrow used for coefficient restriction is the original geometric
transporter; its etaleness is derived from the actual CM geometry. -/
theorem cmSmallLevelTowerEtale :
    ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
  fun k =>
  cmGeometricSchemeTower_map_etale_of_dominantCriterion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q
    existence geometry hRigid criterion k

local notation "towerEtale" => cmSmallLevelTowerEtale D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion

variable (R : Type) [CommRing R]

/-- Compatible module sheaves on the actual geometric CM tower. Etaleness is
supplied by the proved geometric map theorem for these exact inputs. -/
abbrev cmSmallLevelCoefficientDiagram :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  CoefficientDiagram R (geometricSchemes).op

local notation "coefficients" => cmSmallLevelCoefficientDiagram D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- The sheaf-level triviality property on the actual CM coefficient diagrams. -/
def cmSmallLevelTrivialCoefficients : ObjectProperty coefficients :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  RestrictedLevelTowerCohomology.levelTrivialCoefficients (geometricSchemes) R

local notation "trivialCoefficients" => cmSmallLevelTrivialCoefficients D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Degreewise cohomology retains the exact geometric coefficient diagram. -/
abbrev cmSmallLevelCohomology (coeff : coefficients) (d : ℕ) :
    (SmallCMLevel D)ᵒᵖ ⥤ ModuleCat.{0} R :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  coeff.cohomology d

local notation "levelCohomology" => cmSmallLevelCohomology D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
  existence geometry hRigid criterion R

/-- Cohomology of compatible sheaves on the actual geometric CM tower, indexed
by shrinking inclusions of actual sufficiently small levels. -/
def cmSmallLevelCohomologyDiagram (coeff : coefficients) (d : ℕ) :
    (OrderedSmallCMLevel D)ᵒᵖ ⥤ ModuleCat.{0} R :=
  (orderedSmallCMLevelToSmallCMLevel D).op ⋙ levelCohomology coeff d

/-- The concrete inclusion-indexed diagram is the published restricted diagram. -/
theorem cmSmallLevelCohomologyDiagram_eq_restricted (coeff : coefficients) (d : ℕ) :
    cmSmallLevelCohomologyDiagram D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion
      R coeff d = RestrictedLevelColimit.diagram (levelCohomology coeff d) := rfl

/-- Shrinking-level cohomology of the actual geometric CM tower with its
finite-adelic opposite-group action. -/
def cmSmallLevelColimitCohomology (coeff : coefficients) (d : ℕ) :
    Action (ModuleCat.{0} R) G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.colimitCohomology coeff d

/-- Smooth shrinking-level cohomology of compatible level-trivial coefficients.
Coefficient triviality is additional sheaf-level input. -/
def cmSmallLevelSmoothCohomology (coeff : coefficients)
    (hcoeff : trivialCoefficients coeff) (d : ℕ) : SmoothRep.{0, 0, 0} R G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothColimitCohomology coeff hcoeff d

/-- The smooth representation is functorial in compatible level-trivial sheaves
on this exact geometric CM tower. -/
def cmSmallLevelSmoothCohomologyFunctor (d : ℕ) :
    (trivialCoefficients).FullSubcategory ⥤ SmoothRep.{0, 0, 0} R G := by
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothColimitCohomologyFunctor
    (geometricSchemes) R d

/-- Translation acts by the actual geometric transporter from the conjugate
level and that transporter's given coefficient restriction map. -/
theorem cmSmallLevelSmoothCohomology_action (coeff : coefficients)
    (hcoeff : trivialCoefficients coeff) (d : ℕ) (g : G) (U : SmallCMLevel D)
    (x : (levelCohomology coeff d).obj (op U)) :
    letI := D.finite
    letI : Module.Finite ℚ A := Module.Finite.trans F A
    letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
      towerEtale
    (cmSmallLevelSmoothCohomology D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry hRigid criterion
      R coeff hcoeff d).obj.ρ g
        ((RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom x) =
      (RestrictedLevelColimit.ι (levelCohomology coeff d) (restrictedConj small g U)).hom
        ((cohomologyMapWithCoefficients
          ((geometricSchemes).map (restrictedConjArrow small g U)) R d
          (coeff.map (restrictedConjArrow small g U).op)).hom x) := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.smoothColimitCohomology_ρ_ι_apply
    coeff hcoeff d g U x

/-- Provided a small CM level exists, every cohomology class in the shrinking
colimit is represented at one actual small level. -/
theorem cmSmallLevelCohomology_exists_level_class [Nonempty (SmallCMLevel D)]
    (coeff : coefficients) (d : ℕ)
    (x : (colimit (cmSmallLevelCohomologyDiagram D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q
      existence geometry hRigid criterion R coeff d) : ModuleCat.{0} R)) :
    ∃ (U : SmallCMLevel D) (y : (levelCohomology coeff d).obj (op U)),
      (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom y = x := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  exact RestrictedLevelTowerCohomology.exists_level_class coeff d x

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
