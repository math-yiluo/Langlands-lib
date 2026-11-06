import Langlands.Shimura.PEL.HarrisTaylorCMTransporterEtale
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricFiniteEtale

/-! # Finite-etale geometry of every actual geometric CM transporter -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

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

local notation "originalSchemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "projection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "baseChangeSquare" => cmGeometricSchemeTower_map_isPullback D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})

include existence geometry

/-- Every geometric transporter is surjective by base change of the original map. -/
theorem cmGeometricSchemeTower_map_surjective
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Function.Surjective ((geometricSchemes).map k) := by
  let : Surjective ((originalSchemes).map k) :=
    ⟨cmSchemeTower_map_surjective D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q existence geometry k⟩
  let : Surjective ((geometricSchemes).map k) :=
    MorphismProperty.of_isPullback (P := @Surjective) (baseChangeSquare k) inferInstance
  exact ((geometricSchemes).map k).surjective

variable
  (hRigid : ∀ U : SmallCMLevel D,
    CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      compatibility h htor U.obj)
  (criterion : Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0})

include hRigid criterion

local notation "originalCover" => cmFiniteEtaleTransition_of_dominantCriterion D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  existence geometry hRigid criterion q

/-- Etaleness of every actual geometric transporter follows by base change. -/
theorem cmGeometricSchemeTower_map_etale_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Etale ((geometricSchemes).map k) :=
  MorphismProperty.of_isPullback (P := @Etale) (baseChangeSquare k)
    (originalCover k).property.2

/-- Finiteness holds for the same original geometric transporter. -/
theorem cmGeometricSchemeTower_map_isFinite_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    IsFinite ((geometricSchemes).map k) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (baseChangeSquare k)
    (originalCover k).property.1

/-- The existing geometric source and its transporter map form a finite-etale cover. -/
def cmGeometricFiniteEtaleTransition_of_dominantCriterion
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    Cover ((geometricSchemes).obj U) := by
  have : Etale ((geometricSchemes).map k) :=
    cmGeometricSchemeTower_map_etale_of_dominantCriterion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q
      existence geometry hRigid criterion k
  have : IsFinite ((geometricSchemes).map k) :=
    cmGeometricSchemeTower_map_isFinite_of_dominantCriterion D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q
      existence geometry hRigid criterion k
  exact cover ((geometricSchemes).map k)

local notation "geometricCover" => cmGeometricFiniteEtaleTransition_of_dominantCriterion
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q existence geometry hRigid criterion

@[simp] theorem cmGeometricFiniteEtaleTransition_of_dominantCriterion_left
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (geometricCover k).obj.left = (geometricSchemes).obj V := rfl

@[simp] theorem cmGeometricFiniteEtaleTransition_of_dominantCriterion_hom
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (geometricCover k).obj.hom = (geometricSchemes).map k := rfl

/-- The cover on the existing geometric level is canonically the original cover pulled back. -/
def cmGeometricFiniteEtaleTransitionPullbackIso
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    geometricCover k ≅
      (pullbackFunctor ((projection).app U)).obj (originalCover k) :=
  ObjectProperty.isoMk _ (Over.isoMk (baseChangeSquare k).isoPullback
    (baseChangeSquare k).isoPullback_hom_snd)

local notation "coverIso" => cmGeometricFiniteEtaleTransitionPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q existence geometry hRigid criterion

/-- The first projection of the comparison is the original geometric projection. -/
@[reassoc (attr := simp)]
theorem cmGeometricFiniteEtaleTransitionPullbackIso_hom_fst
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (coverIso k).hom.hom.left ≫
      pullback.fst (originalCover k).obj.hom ((projection).app U) =
        (projection).app V :=
  (baseChangeSquare k).isoPullback_hom_fst

/-- The second projection recovers the actual geometric transporter map. -/
@[reassoc (attr := simp)]
theorem cmGeometricFiniteEtaleTransitionPullbackIso_hom_snd
    {U V : SmallCMLevel D} (k : V ⟶ U) :
    (coverIso k).hom.hom.left ≫
      pullback.snd (originalCover k).obj.hom ((projection).app U) =
        (geometricSchemes).map k :=
  (baseChangeSquare k).isoPullback_hom_snd

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
