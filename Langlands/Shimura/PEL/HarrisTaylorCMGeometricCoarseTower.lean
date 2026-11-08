import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientCoarseTower
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseAssociatedSystem
import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem

/-! # Actual inverse image along the original coarse CM coefficient tower -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.Shimura.Coefficients Langlands.Cohomology
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
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

variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)

local notation "chosen" => chosenCMLevelRepresentation D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "overTower" => representedCMOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor chosen
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricOver" => cmGeometricOverTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

local notation "fieldProjection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q

variable (U V T : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  (hTV : T.obj.subgroup ≤ V.obj.subgroup)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor T.obj)

variable (hRigidV : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)

local notation "hTU" => hTV.trans hVU
local notation "XT" => (geometricSchemes).obj T
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "commonLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U T hTU m hm k
local notation "commonh" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U T hTU m hm k
local notation "commonGroups" => cmHarrisCoarseCoefficientGroups D ρ p U T hTU m hm
local notation "commonCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "association" => etaleAssociatedVaryingSystemFunctor («R» := R) XT commonCovers commonProperty
local notation "commonInc" k:arg => cmHarrisGeometricCoarseAssociatedInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid k
local notation "systemT" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "coefficientsT" => cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm
local notation "XV" => (geometricSchemes).obj V
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "pairGroups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "groupMap" => cmHarrisCoarseTowerGroupMap D ρ p U V T hVU hTV m hm
local notation "pairLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "pairh" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U V hVU m hm k
local notation "refinement" k:arg => cmHarrisCoarseTowerLevel_le D ρ p U V T hVU hTV m hm k
local notation "pairCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pulledCovers" => (etaleTorsorDiagramPullback coarseMap pairGroups).obj pairCovers

/-- The actual T-intersection to V-intersection inclusion is the first pullback coordinate. -/
def cmHarrisGeometricCoarseTowerFineMap (k : ℕᵒᵖ) :
    ((commonCovers).obj.obj k).left ⟶ ((pairCovers).obj.obj k).left :=
  (geometricSchemes).map (smallCMInclusion D (refinement k.unop))

local notation "fineMap" k:arg => cmHarrisGeometricCoarseTowerFineMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k

/-- Both original routes from the T-intersection kernel reach the same coarse V level. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerFineMap_projection (k : ℕᵒᵖ) :
    fineMap k ≫ ((pairCovers).obj.obj k).hom =
      ((commonCovers).obj.obj k).hom ≫ coarseMap := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- Map to the literal pullback of the original V-intersection cover along X_T to X_V. -/
def cmHarrisGeometricCoarseTowerPullbackCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (pulledCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    (pullback.lift (fineMap k) (((commonCovers).obj.obj k).hom)
      (cmHarrisGeometricCoarseTowerFineMap_projection D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k))
    (pullback.lift_snd _ _ _)

local notation "coverMap" k:arg => cmHarrisGeometricCoarseTowerPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarseTowerPullbackCoverMap_fst (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.fst ((pairCovers).obj.obj k).hom coarseMap =
      fineMap k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarseTowerPullbackCoverMap_snd (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.snd ((pairCovers).obj.obj k).hom coarseMap =
      ((commonCovers).obj.obj k).hom := pullback.lift_snd _ _ _

/-- Equivariance on the original T representatives follows from actual transporter composition. -/
theorem cmHarrisGeometricCoarseTowerFineMap_equivariant_mk
    (k : ℕᵒᵖ) (g : T.obj.subgroup) :
    ((commonCovers).ρ k (QuotientGroup.mk g)).left ≫ fineMap k =
      fineMap k ≫ ((pairCovers).ρ k
        (((groupMap).app k).hom (QuotientGroup.mk g))).left := by
  change (geometricSchemes).map
      (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
      (geometricSchemes).map (smallCMInclusion D (refinement k.unop)) =
    (geometricSchemes).map (smallCMInclusion D (refinement k.unop)) ≫
      (geometricSchemes).map (smallCMNormalInverseArrow D V (pairLevel k.unop)
        (pairh k.unop) (Subgroup.inclusion hTV g))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp]
  apply congrArg (geometricSchemes).map
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact (mul_one _).trans (one_mul _).symm

/-- The original fine map is equivariant for the constructed T-to-V residual map. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerFineMap_equivariant
    (k : ℕᵒᵖ) (g : (commonGroups).obj k) :
    ((commonCovers).ρ k g).left ≫ fineMap k =
      fineMap k ≫ ((pairCovers).ρ k (((groupMap).app k).hom g)).left := by
  induction g using QuotientGroup.induction_on with
  | H g => exact cmHarrisGeometricCoarseTowerFineMap_equivariant_mk D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k g

/-- The constructed map to the actual fiber product is equivariant. -/
def cmHarrisGeometricCoarseTowerPullbackActionMap (k : ℕᵒᵖ) :
    (commonCovers).action k ⟶
      (Action.res (XT).Etale ((groupMap).app k).hom).obj ((pulledCovers).action k) where
  hom := coverMap k
  comm g := by
    apply MorphismProperty.Over.Hom.ext
    change ((commonCovers).ρ k g).left ≫ (coverMap k).left =
      (coverMap k).left ≫ ((pulledCovers).ρ k (((groupMap).app k).hom g)).left
    have hfst : ((pulledCovers).ρ k (((groupMap).app k).hom g)).left ≫
        pullback.fst ((pairCovers).obj.obj k).hom coarseMap =
      pullback.fst ((pairCovers).obj.obj k).hom coarseMap ≫
        ((pairCovers).ρ k (((groupMap).app k).hom g)).left :=
      etaleTorsorPullbackFunctor_ρ_fst coarseMap
        ((pairCovers).action k) (((groupMap).app k).hom g)
    have hsnd : ((pulledCovers).ρ k (((groupMap).app k).hom g)).left ≫
        pullback.snd ((pairCovers).obj.obj k).hom coarseMap =
      pullback.snd ((pairCovers).obj.obj k).hom coarseMap :=
      etaleTorsorPullbackFunctor_ρ_snd coarseMap
        ((pairCovers).action k) (((groupMap).app k).hom g)
    apply pullback.hom_ext
    · rw [Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_fst,
        Category.assoc, hfst,
        ← Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_fst]
      exact cmHarrisGeometricCoarseTowerFineMap_equivariant D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k g
    · rw [Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_snd,
        Category.assoc, hsnd,
        cmHarrisGeometricCoarseTowerPullbackCoverMap_snd]
      exact MorphismProperty.Over.w ((commonCovers).ρ k g)

/-- The actual original level inclusions commute with every exponent reduction. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerFineMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonCovers).obj.map f).left ≫ fineMap j =
      fineMap i ≫ ((pairCovers).obj.map f).left := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarseTowerPulledMap_fst
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledCovers).obj.map f).left ≫
        pullback.fst ((pairCovers).obj.obj j).hom coarseMap =
      pullback.fst ((pairCovers).obj.obj i).hom coarseMap ≫
        ((pairCovers).obj.map f).left := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmHarrisGeometricCoarseTowerPulledMap_snd
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledCovers).obj.map f).left ≫
        pullback.snd ((pairCovers).obj.obj j).hom coarseMap =
      pullback.snd ((pairCovers).obj.obj i).hom coarseMap := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- All literal pullback comparison components retain the original exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerPullbackCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ coverMap j =
      coverMap i ≫ (pulledCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change ((commonCovers).obj.map f).left ≫ (coverMap j).left =
    (coverMap i).left ≫ ((pulledCovers).obj.map f).left
  apply pullback.hom_ext
  · rw [Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_fst,
      Category.assoc, cmHarrisGeometricCoarseTowerPulledMap_fst,
      ← Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_fst]
    exact cmHarrisGeometricCoarseTowerFineMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV f
  · rw [Category.assoc, cmHarrisGeometricCoarseTowerPullbackCoverMap_snd,
      Category.assoc, cmHarrisGeometricCoarseTowerPulledMap_snd,
      cmHarrisGeometricCoarseTowerPullbackCoverMap_snd]
    exact MorphismProperty.Over.w ((commonCovers).obj.map f)

/-- A map of complete original cover diagrams along the actual coarse-tower residual map. -/
def cmHarrisGeometricCoarseTowerPullbackDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale groupMap).obj pulledCovers where
  hom :=
    { app k := coverMap k
      naturality _ _ f := cmHarrisGeometricCoarseTowerPullbackCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV f }
  comm k g := (cmHarrisGeometricCoarseTowerPullbackActionMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k).comm g

local notation "diagramMap" => cmHarrisGeometricCoarseTowerPullbackDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "pulledProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor
  coarseMap pairGroups pairCovers pairProperty
local notation "coverIso" => etaleAssociatedVaryingGroupCoverIso XT R groupMap
  commonCovers pulledCovers diagramMap commonProperty pulledProperty
local notation "coefficientsV" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm
local notation "coefficientIso" => cmHarrisCoarseTowerCoefficientIso D ρ p U V T hVU hTV m hm
local notation "systemV" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pulledSystem" => etaleAssociatedVaryingSystem XT pulledCovers pulledProperty coefficientsV
local notation "pulledInc" k:arg => etaleAssociatedInclusion XT ((pulledCovers).action k) ((coefficientsV).action k)

/-- Actual group/cover change and the coefficient identity identify the entire coarse systems. -/
def cmHarrisGeometricCoarseTowerCoverIso : pulledSystem ≅ systemT :=
  (coverIso).app coefficientsV ≪≫ (association).mapIso coefficientIso

local notation "towerCoverIso" => cmHarrisGeometricCoarseTowerCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- The coefficient identification is identity, so the upper comparison changes only the cover. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    (towerCoverIso).hom.app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledCovers).action k) ((coefficientsV).action k) ≫
        coverPullback J (coverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficientsV).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (coefficientIso).hom)
  change ((association).map (coefficientIso).hom).app k ≫ commonInc k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) groupMap).obj
        coefficientsV).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) groupMap).obj
        coefficientsV).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) groupMap).obj
        coefficientsV).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((coverIso).hom.app coefficientsV).app k ≫
      ((association).map (coefficientIso).hom).app k) ≫ commonInc k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R groupMap commonCovers
    pulledCovers diagramMap k coefficientsV

/-- Genuine inverse image of the original coarse(U,V) associated system along X_T to X_V. -/
def cmHarrisGeometricCoarseTowerInverseSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  systemV ⋙ inverseImage coarseMap R

local notation "inverseSystem" => cmHarrisGeometricCoarseTowerInverseSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigidV

/-- Genuine inverse image agrees with the original coarse(U,T) system at every exponent. -/
def cmHarrisGeometricCoarseTowerInverseIso : inverseSystem ≅ systemT :=
  (etaleAssociatedVaryingSystemInverseImage coarseMap R pairCovers pairProperty).app
    coefficientsV ≪≫ towerCoverIso

local notation "towerInverseIso" => cmHarrisGeometricCoarseTowerInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- The inverse comparison retains every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerInverseIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (systemT).map f ≫ (towerInverseIso).inv.app j =
      (towerInverseIso).inv.app i ≫ (inverseImage coarseMap R).map ((systemV).map f) :=
  (towerInverseIso).inv.naturality f

/-- Every original transition is preserved in the forward comparison. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerInverseIso_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (inverseImage coarseMap R).map ((systemV).map f) ≫ (towerInverseIso).hom.app j =
      (towerInverseIso).hom.app i ≫ (systemT).map f :=
  (towerInverseIso).hom.naturality f

/-- The actual inverse-image comparison retains its original product, coefficient and cover coordinates. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerInverseIso_hom_inclusion (k : ℕᵒᵖ) :
    (towerInverseIso).hom.app k ≫ commonInc k =
      (inverseImage coarseMap R).map
        (cmHarrisGeometricCoarseAssociatedInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k) ≫
      (inverseImageProductSheafIso coarseMap R ((pairCovers).action k) (pairProperty k)
        ((constantSheaf (Scheme.smallEtaleTopology XV) (ModuleCat.{0} R)).obj
          ((coefficientsV).obj.obj k))).hom ≫
      (productSheaf J ((pulledCovers).obj.obj k)).map
        ((inverseImageConstantIso coarseMap R).hom.app ((coefficientsV).obj.obj k)) ≫
      coverPullback J (coverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficientsV).obj.obj k)) := by
  change ((inverseImageConstantAssociatedIso coarseMap R ((pairCovers).action k)
    (pairProperty k)).hom.app ((coefficientsV).action k) ≫
      (towerCoverIso).hom.app k) ≫ commonInc k = _
  rw [Category.assoc, cmHarrisGeometricCoarseTowerCoverIso_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k]
  exact inverseImageConstantAssociatedIso_hom_inclusion_assoc coarseMap R
    ((pairCovers).action k) (pairProperty k) ((coefficientsV).action k) _

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
