import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientUpperPair
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricTripleCommon
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeComparison
import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem

/-! # Actual inverse image of the original upper pair on triple CM covers -/

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

section Transporters

variable (U V P Q : SmallCMLevel D)
  (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  (hPV : P.obj.subgroup ≤ V.obj.subgroup)
  (hQU : Q.obj.subgroup ≤ U.obj.subgroup)
  (hPQ : P.obj.subgroup ≤ Q.obj.subgroup)
  [(P.obj.subgroup.subgroupOf V.obj.subgroup).Normal]
  [(Q.obj.subgroup.subgroupOf U.obj.subgroup).Normal]

omit [IsCMField F] [IsScalarTower E F A] [IsScalarTower ℚ F A] in
/-- Inverse translation commutes with inclusion even when the ambient deck level changes. -/
theorem smallCMNormalInverseArrow_ambient_inclusion (g : V.obj.subgroup) :
    smallCMNormalInverseArrow D V P hPV g ≫ smallCMInclusion D hPQ =
      smallCMInclusion D hPQ ≫
        smallCMNormalInverseArrow D U Q hQU (Subgroup.inclusion hVU g) := by
  apply ObjectProperty.hom_ext
  apply CompactOpenLevel.Arrow.ext
  exact (mul_one _).trans (one_mul _).symm

end Transporters

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
local notation "commonLevel" k:arg => cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm k
local notation "commonh" k:arg => cmHarrisTripleCommonLevel_le D ρ p U V T hVU hTV m hm k
local notation "commonGroups" => cmHarrisTripleCommonGroups D ρ p U V T hVU hTV m hm
local notation "commonCovers" => cmHarrisGeometricTripleCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonChain" => cmHarrisGeometricTripleCommonSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonInc" a:arg k:arg => cmHarrisGeometricTripleCommonSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid a k

local notation "XV" => (geometricSchemes).obj V
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "pairGroups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "groupMap" => cmHarrisTripleUpperPairGroupMap D ρ p U V T hVU hTV m hm
local notation "pairLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p U V hVU m hm k
local notation "pairh" k:arg => cmHarrisLatticeCommonLevel_le D ρ p U V hVU m hm k
local notation "refinement" k:arg => cmHarrisTripleCommonLevel_le_upperPair D ρ p U V T hVU hTV m hm k
local notation "pairCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pulledCovers" => (etaleTorsorDiagramPullback coarseMap pairGroups).obj pairCovers

/-- The actual triple-to-upper-pair inclusion is the first pullback coordinate. -/
def cmHarrisGeometricTripleUpperPairFineMap (k : ℕᵒᵖ) :
    ((commonCovers).obj.obj k).left ⟶ ((pairCovers).obj.obj k).left :=
  (geometricSchemes).map (smallCMInclusion D (refinement k.unop))

local notation "fineMap" k:arg => cmHarrisGeometricTripleUpperPairFineMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k

/-- Both original routes from the triple kernel reach the same coarse V level. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairFineMap_projection (k : ℕᵒᵖ) :
    fineMap k ≫ ((pairCovers).obj.obj k).hom =
      ((commonCovers).obj.obj k).hom ≫ coarseMap := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- Map to the literal pullback of the original upper-pair cover along X_T to X_V. -/
def cmHarrisGeometricTripleUpperPairPullbackCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (pulledCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    (pullback.lift (fineMap k) (((commonCovers).obj.obj k).hom)
      (cmHarrisGeometricTripleUpperPairFineMap_projection D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k))
    (pullback.lift_snd _ _ _)

local notation "coverMap" k:arg => cmHarrisGeometricTripleUpperPairPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k

@[reassoc (attr := simp)] theorem cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.fst ((pairCovers).obj.obj k).hom coarseMap =
      fineMap k := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd (k : ℕᵒᵖ) :
    (coverMap k).left ≫ pullback.snd ((pairCovers).obj.obj k).hom coarseMap =
      ((commonCovers).obj.obj k).hom := pullback.lift_snd _ _ _

/-- Equivariance on the original T representatives follows from actual transporter composition. -/
theorem cmHarrisGeometricTripleUpperPairFineMap_equivariant_mk
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
  exact congrArg (geometricSchemes).map
    (smallCMNormalInverseArrow_ambient_inclusion D V T
      (commonLevel k.unop) (pairLevel k.unop) hTV (commonh k.unop)
      (pairh k.unop) (refinement k.unop) g)

/-- The original fine map is equivariant for the constructed T-to-V residual map. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairFineMap_equivariant
    (k : ℕᵒᵖ) (g : (commonGroups).obj k) :
    ((commonCovers).ρ k g).left ≫ fineMap k =
      fineMap k ≫ ((pairCovers).ρ k (((groupMap).app k).hom g)).left := by
  induction g using QuotientGroup.induction_on with
  | H g => exact cmHarrisGeometricTripleUpperPairFineMap_equivariant_mk D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k g

/-- The constructed map to the actual fiber product is equivariant. -/
def cmHarrisGeometricTripleUpperPairPullbackActionMap (k : ℕᵒᵖ) :
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
    · rw [Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst,
        Category.assoc, hfst,
        ← Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst]
      exact cmHarrisGeometricTripleUpperPairFineMap_equivariant D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k g
    · rw [Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd,
        Category.assoc, hsnd,
        cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd]
      exact MorphismProperty.Over.w ((commonCovers).ρ k g)

/-- The actual original level inclusions commute with every exponent reduction. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairFineMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonCovers).obj.map f).left ≫ fineMap j =
      fineMap i ≫ ((pairCovers).obj.map f).left := by
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

@[reassoc (attr := simp)] theorem cmHarrisGeometricTripleUpperPairPulledMap_fst
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledCovers).obj.map f).left ≫
        pullback.fst ((pairCovers).obj.obj j).hom coarseMap =
      pullback.fst ((pairCovers).obj.obj i).hom coarseMap ≫
        ((pairCovers).obj.map f).left := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem cmHarrisGeometricTripleUpperPairPulledMap_snd
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((pulledCovers).obj.map f).left ≫
        pullback.snd ((pairCovers).obj.obj j).hom coarseMap =
      pullback.snd ((pairCovers).obj.obj i).hom coarseMap := by
  change (pullback.lift _ _ _) ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- All literal pullback comparison components retain the original exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairPullbackCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ coverMap j =
      coverMap i ≫ (pulledCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change ((commonCovers).obj.map f).left ≫ (coverMap j).left =
    (coverMap i).left ≫ ((pulledCovers).obj.map f).left
  apply pullback.hom_ext
  · rw [Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst,
      Category.assoc, cmHarrisGeometricTripleUpperPairPulledMap_fst,
      ← Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst]
    exact cmHarrisGeometricTripleUpperPairFineMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV f
  · rw [Category.assoc, cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd,
      Category.assoc, cmHarrisGeometricTripleUpperPairPulledMap_snd,
      cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd]
    exact MorphismProperty.Over.w ((commonCovers).obj.map f)

/-- A map of complete original cover diagrams along the actual upper-pair residual map. -/
def cmHarrisGeometricTripleUpperPairPullbackDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale groupMap).obj pulledCovers where
  hom :=
    { app k := coverMap k
      naturality _ _ f := cmHarrisGeometricTripleUpperPairPullbackCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV f }
  comm k g := (cmHarrisGeometricTripleUpperPairPullbackActionMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k).comm g

local notation "diagramMap" => cmHarrisGeometricTripleUpperPairPullbackDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "pulledProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor
  coarseMap pairGroups pairCovers pairProperty
local notation "coverIso" => etaleAssociatedVaryingGroupCoverIso XT R groupMap
  commonCovers pulledCovers diagramMap commonProperty pulledProperty
local notation "inverseCoverIso" =>
  etaleAssociatedVaryingSystemInverseImage coarseMap R pairCovers pairProperty ≪≫ coverIso
local notation "ownCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "originalCoefficients" => cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm
local notation "ownCoefficientIso" => cmHarrisTripleUpperPairOwnCoefficientIso D ρ p U V T hVU hTV m hm
local notation "originalCoefficientIso" => cmHarrisTripleUpperPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm
local notation "coefficientInclusion" => cmHarrisLatticeCommonCoefficientInclusion D ρ p U V hVU m hm
local notation "pairOwnSystem" => cmHarrisGeometricLatticeCommonOwnSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairOriginalSystem" => cmHarrisGeometricLatticeCommonOriginalSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV

/-- Genuine inverse image of the entire original upper-pair own system. -/
def cmHarrisGeometricTripleUpperPairOwnInverseSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  pairOwnSystem ⋙ inverseImage coarseMap R

/-- Genuine inverse image of the entire original upper-pair original system. -/
def cmHarrisGeometricTripleUpperPairOriginalInverseSystem : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R) :=
  pairOriginalSystem ⋙ inverseImage coarseMap R

local notation "ownInverseSystem" => cmHarrisGeometricTripleUpperPairOwnInverseSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigidV
local notation "originalInverseSystem" => cmHarrisGeometricTripleUpperPairOriginalInverseSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigidV

/-- Actual inverse image, cover change and unchanged coefficients identify the middle triple vertex. -/
def cmHarrisGeometricTripleUpperPairOwnInverseIso :
    ownInverseSystem ≅ (commonChain).obj' 1 :=
  (inverseCoverIso).app ownCoefficients ≪≫ (association).mapIso ownCoefficientIso

/-- The same construction identifies the upper triple vertex with the original U coefficients. -/
def cmHarrisGeometricTripleUpperPairOriginalInverseIso :
    originalInverseSystem ≅ (commonChain).obj' 2 :=
  (inverseCoverIso).app originalCoefficients ≪≫ (association).mapIso originalCoefficientIso

local notation "ownIso" => cmHarrisGeometricTripleUpperPairOwnInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "originalIso" => cmHarrisGeometricTripleUpperPairOriginalInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- Inverse image of the original pair lattice inclusion is the original triple upper inclusion. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairInverseInclusion_square :
    Functor.whiskerRight pairInclusion (inverseImage coarseMap R) ≫ (originalIso).hom =
      (ownIso).hom ≫
        (association).map (cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm) := by
  change _ ≫ ((inverseCoverIso).app originalCoefficients).hom ≫
      (association).map (originalCoefficientIso).hom =
    (((inverseCoverIso).app ownCoefficients).hom ≫
      (association).map (ownCoefficientIso).hom) ≫
        (association).map (cmHarrisTripleUpperCoefficientInclusion D ρ p U V T hVU hTV m hm)
  have hn : Functor.whiskerRight pairInclusion (inverseImage coarseMap R) ≫
      ((inverseCoverIso).app originalCoefficients).hom =
    ((inverseCoverIso).app ownCoefficients).hom ≫
      (association).map
        ((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) groupMap).map
          coefficientInclusion) :=
    (inverseCoverIso).hom.naturality coefficientInclusion
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (association).map_comp,
    cmHarrisTripleUpperPairCoefficientInclusion_square, (association).map_comp]

/-- The inverse middle comparison retains every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairOwnInverseIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 1).map f ≫ (ownIso).inv.app j =
      (ownIso).inv.app i ≫ (inverseImage coarseMap R).map ((pairOwnSystem).map f) :=
  (ownIso).inv.naturality f

/-- The inverse upper comparison likewise retains the complete original U coefficient system. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperPairOriginalInverseIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 2).map f ≫ (originalIso).inv.app j =
      (originalIso).inv.app i ≫ (inverseImage coarseMap R).map ((pairOriginalSystem).map f) :=
  (originalIso).inv.naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
