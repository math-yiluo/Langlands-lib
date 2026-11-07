import Langlands.Shimura.PEL.HarrisTaylorCMGeometricTripleCommon
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientPairTriple
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeComparison

/-! # Original pair systems on the actual triple geometric CM covers -/

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
open Langlands.Geometry

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

local notation "hTU" => hTV.trans hVU
local notation "XT" => (geometricSchemes).obj T
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "commonLevel" k:arg => cmHarrisTripleCommonLevel D ρ p U V T hVU hTV m hm k
local notation "commonh" k:arg => cmHarrisTripleCommonLevel_le D ρ p U V T hVU hTV m hm k
local notation "commonGroups" => cmHarrisTripleCommonGroups D ρ p U V T hVU hTV m hm
local notation "commonCovers" => cmHarrisGeometricTripleCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonChain" => cmHarrisGeometricTripleCommonSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonInc" a:arg k:arg => cmHarrisGeometricTripleCommonSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid a k

local notation "directGroupMap" => cmHarrisTripleDirectPairGroupMap D ρ p U V T hVU hTV m hm
local notation "directCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directAssociation" => cmHarrisGeometricLatticeCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p U T hTU m hm k
local notation "directh" k:arg => cmHarrisLatticeCommonLevel_le D ρ p U T hTU m hm k
local notation "directRefinement" k:arg => cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k
local notation "directOwnCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p U T hTU m hm
local notation "directOriginalCoefficients" => cmHarrisLatticeCommonOriginalCoefficients D ρ p U T hTU m hm
local notation "directOwnSystem" => cmHarrisGeometricLatticeCommonOwnSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directOriginalSystem" => cmHarrisGeometricLatticeCommonOriginalSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directCoefficientInclusion" => cmHarrisLatticeCommonCoefficientInclusion D ρ p U T hTU m hm
local notation "directOwnCoefficientIso" => cmHarrisTripleDirectPairOwnCoefficientIso D ρ p U V T hVU hTV m hm
local notation "directOriginalCoefficientIso" => cmHarrisTripleDirectPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm

/-- Actual geometric forgetting from the triple kernel to the original direct pair kernel. -/
def cmHarrisGeometricTripleDirectPairCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (directCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (directRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (directRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (directh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "directCoverMap" k:arg => cmHarrisGeometricTripleDirectPairCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k

@[simp] theorem cmHarrisGeometricTripleDirectPairCoverMap_left (k : ℕᵒᵖ) :
    (directCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (directRefinement k.unop)) := rfl

/-- The same original tower maps commute with every exponent reduction. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ directCoverMap j =
      directCoverMap i ≫ (directCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (directRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (directRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisLatticeCommonLevel_antitone D ρ p U T hTU m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The full actual cover map is equivariant along the actual triple-to-pair quotient homomorphisms. -/
def cmHarrisGeometricTripleDirectPairCoverDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale directGroupMap).obj directCovers where
  hom :=
    { app k := directCoverMap k
      naturality _ _ f := by
        exact cmHarrisGeometricTripleDirectPairCoverMap_naturality D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid f }
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (directRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (directRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (directLevel k.unop) (directh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "directDiagramMap" => cmHarrisGeometricTripleDirectPairCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "directCoverIso" => etaleAssociatedVaryingGroupCoverIso XT R directGroupMap
  commonCovers directCovers directDiagramMap commonProperty directProperty

/-- Changing the actual cover and identifying the unchanged own coefficients gives a whole-system isomorphism. -/
def cmHarrisGeometricTripleDirectPairOwnSystemIso :
    directOwnSystem ≅ (commonChain).obj' 0 :=
  (directCoverIso).app directOwnCoefficients ≪≫
    (association).mapIso directOwnCoefficientIso

/-- The same construction retains the original larger lattice and every exponent reduction. -/
def cmHarrisGeometricTripleDirectPairOriginalSystemIso :
    directOriginalSystem ≅ (commonChain).obj' 2 :=
  (directCoverIso).app directOriginalCoefficients ≪≫
    (association).mapIso directOriginalCoefficientIso

local notation "directOwnIso" => cmHarrisGeometricTripleDirectPairOwnSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "directOriginalIso" => cmHarrisGeometricTripleDirectPairOriginalSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- This comparison pulls only the actual cover coordinate and retains the original own coefficient. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOwnSystemIso_inclusion (k : ℕᵒᵖ) :
    (directOwnIso).hom.app k ≫ commonInc 0 k =
      etaleAssociatedInclusion XT ((directCovers).action k) ((directOwnCoefficients).action k) ≫
        coverPullback J (directCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((directOwnCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (directOwnCoefficientIso).hom)
  change ((association).map (directOwnCoefficientIso).hom).app k ≫ commonInc 0 k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOwnCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOwnCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOwnCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((directCoverIso).hom.app directOwnCoefficients).app k ≫
      ((association).map (directOwnCoefficientIso).hom).app k) ≫ commonInc 0 k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R directGroupMap commonCovers directCovers
    directDiagramMap k directOwnCoefficients

/-- This comparison pulls only the actual cover coordinate and retains the original larger-lattice coefficient. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOriginalSystemIso_inclusion (k : ℕᵒᵖ) :
    (directOriginalIso).hom.app k ≫ commonInc 2 k =
      etaleAssociatedInclusion XT ((directCovers).action k) ((directOriginalCoefficients).action k) ≫
        coverPullback J (directCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((directOriginalCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (directOriginalCoefficientIso).hom)
  change ((association).map (directOriginalCoefficientIso).hom).app k ≫ commonInc 2 k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOriginalCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOriginalCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).obj
        directOriginalCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((directCoverIso).hom.app directOriginalCoefficients).app k ≫
      ((association).map (directOriginalCoefficientIso).hom).app k) ≫ commonInc 2 k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R directGroupMap commonCovers directCovers
    directDiagramMap k directOriginalCoefficients

/-- The isomorphism's inverse retains the full original own coefficient transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOwnSystemIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 0).map f ≫ (directOwnIso).inv.app j =
      (directOwnIso).inv.app i ≫ (directOwnSystem).map f :=
  (directOwnIso).inv.naturality f

/-- The original larger-lattice transitions are likewise unchanged. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOriginalSystemIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 2).map f ≫ (directOriginalIso).inv.app j =
      (directOriginalIso).inv.app i ≫ (directOriginalSystem).map f :=
  (directOriginalIso).inv.naturality f

/-- The descended original pair inclusion is the original triple inclusion through these cover comparisons. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairSystemInclusion_square :
    directInclusion ≫ (directOriginalIso).hom =
      (directOwnIso).hom ≫
        (association).map (cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm) := by
  change (directAssociation).map directCoefficientInclusion ≫
      ((directCoverIso).app directOriginalCoefficients).hom ≫
        (association).map (directOriginalCoefficientIso).hom =
    (((directCoverIso).app directOwnCoefficients).hom ≫
      (association).map (directOwnCoefficientIso).hom) ≫
        (association).map (cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm)
  have hn : (directAssociation).map directCoefficientInclusion ≫
      ((directCoverIso).app directOriginalCoefficients).hom =
    ((directCoverIso).app directOwnCoefficients).hom ≫
      (association).map
        ((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) directGroupMap).map
          directCoefficientInclusion) :=
    (directCoverIso).hom.naturality directCoefficientInclusion
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (association).map_comp,
    cmHarrisTripleDirectPairCoefficientInclusion_square, (association).map_comp]

local notation "lowerGroupMap" => cmHarrisTripleLowerPairGroupMap D ρ p U V T hVU hTV m hm
local notation "lowerCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerAssociation" => cmHarrisGeometricLatticeCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p V T hTV m hm k
local notation "lowerh" k:arg => cmHarrisLatticeCommonLevel_le D ρ p V T hTV m hm k
local notation "lowerRefinement" k:arg => cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k
local notation "lowerOwnCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p V T hTV m hm
local notation "lowerOriginalCoefficients" => cmHarrisLatticeCommonOriginalCoefficients D ρ p V T hTV m hm
local notation "lowerOwnSystem" => cmHarrisGeometricLatticeCommonOwnSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerOriginalSystem" => cmHarrisGeometricLatticeCommonOriginalSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerCoefficientInclusion" => cmHarrisLatticeCommonCoefficientInclusion D ρ p V T hTV m hm
local notation "lowerOwnCoefficientIso" => cmHarrisTripleLowerPairOwnCoefficientIso D ρ p U V T hVU hTV m hm
local notation "lowerOriginalCoefficientIso" => cmHarrisTripleLowerPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm

/-- Actual geometric forgetting from the triple kernel to the original lower pair kernel. -/
def cmHarrisGeometricTripleLowerPairCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (lowerCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (lowerRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (lowerRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (lowerh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "lowerCoverMap" k:arg => cmHarrisGeometricTripleLowerPairCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k

@[simp] theorem cmHarrisGeometricTripleLowerPairCoverMap_left (k : ℕᵒᵖ) :
    (lowerCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (lowerRefinement k.unop)) := rfl

/-- The same original tower maps commute with every exponent reduction. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ lowerCoverMap j =
      lowerCoverMap i ≫ (lowerCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (lowerRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (lowerRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisLatticeCommonLevel_antitone D ρ p V T hTV m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The full actual cover map is equivariant along the actual triple-to-pair quotient homomorphisms. -/
def cmHarrisGeometricTripleLowerPairCoverDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale lowerGroupMap).obj lowerCovers where
  hom :=
    { app k := lowerCoverMap k
      naturality _ _ f := by
        exact cmHarrisGeometricTripleLowerPairCoverMap_naturality D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid f }
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (lowerRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (lowerRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (lowerLevel k.unop) (lowerh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "lowerDiagramMap" => cmHarrisGeometricTripleLowerPairCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "lowerCoverIso" => etaleAssociatedVaryingGroupCoverIso XT R lowerGroupMap
  commonCovers lowerCovers lowerDiagramMap commonProperty lowerProperty

/-- Changing the actual cover and identifying the unchanged own coefficients gives a whole-system isomorphism. -/
def cmHarrisGeometricTripleLowerPairOwnSystemIso :
    lowerOwnSystem ≅ (commonChain).obj' 0 :=
  (lowerCoverIso).app lowerOwnCoefficients ≪≫
    (association).mapIso lowerOwnCoefficientIso

/-- The same construction retains the original larger lattice and every exponent reduction. -/
def cmHarrisGeometricTripleLowerPairOriginalSystemIso :
    lowerOriginalSystem ≅ (commonChain).obj' 1 :=
  (lowerCoverIso).app lowerOriginalCoefficients ≪≫
    (association).mapIso lowerOriginalCoefficientIso

local notation "lowerOwnIso" => cmHarrisGeometricTripleLowerPairOwnSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "lowerOriginalIso" => cmHarrisGeometricTripleLowerPairOriginalSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- This comparison pulls only the actual cover coordinate and retains the original own coefficient. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOwnSystemIso_inclusion (k : ℕᵒᵖ) :
    (lowerOwnIso).hom.app k ≫ commonInc 0 k =
      etaleAssociatedInclusion XT ((lowerCovers).action k) ((lowerOwnCoefficients).action k) ≫
        coverPullback J (lowerCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((lowerOwnCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (lowerOwnCoefficientIso).hom)
  change ((association).map (lowerOwnCoefficientIso).hom).app k ≫ commonInc 0 k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOwnCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOwnCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOwnCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((lowerCoverIso).hom.app lowerOwnCoefficients).app k ≫
      ((association).map (lowerOwnCoefficientIso).hom).app k) ≫ commonInc 0 k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R lowerGroupMap commonCovers lowerCovers
    lowerDiagramMap k lowerOwnCoefficients

/-- This comparison pulls only the actual cover coordinate and retains the original larger-lattice coefficient. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOriginalSystemIso_inclusion (k : ℕᵒᵖ) :
    (lowerOriginalIso).hom.app k ≫ commonInc 1 k =
      etaleAssociatedInclusion XT ((lowerCovers).action k) ((lowerOriginalCoefficients).action k) ≫
        coverPullback J (lowerCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((lowerOriginalCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (lowerOriginalCoefficientIso).hom)
  change ((association).map (lowerOriginalCoefficientIso).hom).app k ≫ commonInc 1 k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOriginalCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOriginalCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).obj
        lowerOriginalCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((lowerCoverIso).hom.app lowerOriginalCoefficients).app k ≫
      ((association).map (lowerOriginalCoefficientIso).hom).app k) ≫ commonInc 1 k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R lowerGroupMap commonCovers lowerCovers
    lowerDiagramMap k lowerOriginalCoefficients

/-- The isomorphism's inverse retains the full original own coefficient transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOwnSystemIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 0).map f ≫ (lowerOwnIso).inv.app j =
      (lowerOwnIso).inv.app i ≫ (lowerOwnSystem).map f :=
  (lowerOwnIso).inv.naturality f

/-- The original larger-lattice transitions are likewise unchanged. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOriginalSystemIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 1).map f ≫ (lowerOriginalIso).inv.app j =
      (lowerOriginalIso).inv.app i ≫ (lowerOriginalSystem).map f :=
  (lowerOriginalIso).inv.naturality f

/-- The descended original pair inclusion is the original triple inclusion through these cover comparisons. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairSystemInclusion_square :
    lowerInclusion ≫ (lowerOriginalIso).hom =
      (lowerOwnIso).hom ≫
        (association).map (cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm) := by
  change (lowerAssociation).map lowerCoefficientInclusion ≫
      ((lowerCoverIso).app lowerOriginalCoefficients).hom ≫
        (association).map (lowerOriginalCoefficientIso).hom =
    (((lowerCoverIso).app lowerOwnCoefficients).hom ≫
      (association).map (lowerOwnCoefficientIso).hom) ≫
        (association).map (cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm)
  have hn : (lowerAssociation).map lowerCoefficientInclusion ≫
      ((lowerCoverIso).app lowerOriginalCoefficients).hom =
    ((lowerCoverIso).app lowerOwnCoefficients).hom ≫
      (association).map
        ((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) lowerGroupMap).map
          lowerCoefficientInclusion) :=
    (lowerCoverIso).hom.naturality lowerCoefficientInclusion
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← (association).map_comp,
    cmHarrisTripleLowerPairCoefficientInclusion_square, (association).map_comp]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
