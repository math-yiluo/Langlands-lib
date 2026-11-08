import Langlands.Shimura.PEL.HarrisTaylorCMGeometricUpperPairCoherence
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseTower
import Langlands.Shimura.Coefficients.EtaleInverseImageGroupCoverChange

/-! # Normalization of the original coefficient upper-pair inverse-image endpoint -/

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

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
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
local notation "XV" => (geometricSchemes).obj V
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "pullSystems" => (Functor.whiskeringRight ℕᵒᵖ _ _).obj (inverseImage coarseMap R)
local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleUpperIso" => cmHarrisGeometricTripleUpperCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "pairOriginalIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "originalInverseIso" => cmHarrisGeometricTripleUpperPairOriginalInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

local notation "pairGroups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "pairCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "originalGroups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "originalGroupMap" => cmHarrisLatticeCommonCoarseGroupMap D ρ p U V hVU m hm
local notation "originalCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "originalProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "originalCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm
local notation "pairOriginalCoefficients" => cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm
local notation "pairOriginalCoverMap" k:arg => cmHarrisGeometricLatticeCommonCoarseCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k
local notation "pairOriginalActionMap" k:arg => cmHarrisGeometricLatticeCommonCoarseActionMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k
local notation "commonCovers" => cmHarrisGeometricTripleCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonInc" k:arg => cmHarrisGeometricTripleCommonSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid 2 k
local notation "upperGroupMap" => cmHarrisTripleUpperPairGroupMap D ρ p U V T hVU hTV m hm
local notation "upperCoverMap" k:arg => cmHarrisGeometricTripleUpperPairPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k
local notation "upperDiagramMap" => cmHarrisGeometricTripleUpperPairPullbackDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "originalCoefficientIso" => cmHarrisTripleUpperPairOriginalCoefficientIso D ρ p U V T hVU hTV m hm
local notation "originalCoverMap" k:arg => cmHarrisGeometricTripleUpperCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "coarseCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm
local notation "coarseCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "towerCoverMap" k:arg => cmHarrisGeometricCoarseTowerPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k
local notation "towerCoverIso" => cmHarrisGeometricCoarseTowerCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "towerInverseIso" => cmHarrisGeometricCoarseTowerInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "originalSeparateIso" => cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- Package the original coarse-cover map and every original exponent transition. -/
def cmHarrisGeometricUpperPairOriginalCoverDiagramMap :
    pairCovers ⟶ (EquivariantDiagram.groupRestriction (XV).Etale originalGroupMap).obj originalCovers where
  hom :=
    { app k := pairOriginalCoverMap k
      naturality _ _ f := cmHarrisGeometricLatticeCommonCoarseCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV f }
  comm k g := (pairOriginalActionMap k).comm g

local notation "originalDiagramMap" => cmHarrisGeometricUpperPairOriginalCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pulledPairCovers" => (etaleTorsorDiagramPullback coarseMap pairGroups).obj pairCovers
local notation "pulledOriginalCovers" => (etaleTorsorDiagramPullback coarseMap originalGroups).obj originalCovers
local notation "pulledPairProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor coarseMap pairGroups pairCovers pairProperty
local notation "pulledOriginalProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor coarseMap originalGroups originalCovers originalProperty
local notation "pulledOriginalMap" => etaleGroupCoverMapPullback coarseMap originalGroupMap pairCovers originalCovers originalDiagramMap
local notation "pulledOriginalIso" => etaleAssociatedVaryingGroupCoverIso XT R originalGroupMap pulledPairCovers pulledOriginalCovers pulledOriginalMap pulledPairProperty pulledOriginalProperty
local notation "upperCoverIso" => etaleAssociatedVaryingGroupCoverIso XT R upperGroupMap commonCovers pulledPairCovers upperDiagramMap commonProperty pulledPairProperty
local notation "inverseOriginal" => (etaleAssociatedVaryingSystemInverseImage coarseMap R originalCovers originalProperty).app originalCoefficients
local notation "inversePairOriginal" => (etaleAssociatedVaryingSystemInverseImage coarseMap R pairCovers pairProperty).app pairOriginalCoefficients

/-- The original coarse-cover system isomorphism satisfies the generic genuine inverse-image square. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalCover_inverseImage :
    (pullSystems).map (pairOriginalIso).hom ≫ (inversePairOriginal).hom =
      (inverseOriginal).hom ≫ (pulledOriginalIso).hom.app originalCoefficients :=
  etaleAssociatedVaryingGroupCoverIso_inverseImage_hom coarseMap R originalGroupMap
    pairCovers originalCovers originalDiagramMap pairProperty originalProperty originalCoefficients

/-- The two actual routes into the same pulled original coarse cover agree. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalPullbackCover_comp (k : ℕᵒᵖ) :
    upperCoverMap k ≫ (etaleObjectPullback coarseMap).map (pairOriginalCoverMap k) =
      originalCoverMap k ≫ towerCoverMap k := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · have hp := etaleTorsorPullbackFunctor_map_fst coarseMap (pairOriginalActionMap k)
    change ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k)).left ≫
      pullback.fst ((originalCovers).obj.obj k).hom coarseMap =
        pullback.fst ((pairCovers).obj.obj k).hom coarseMap ≫
          (pairOriginalCoverMap k).left at hp
    change ((upperCoverMap k).left ≫
        ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k)).left) ≫
          pullback.fst ((originalCovers).obj.obj k).hom coarseMap =
      ((originalCoverMap k).left ≫ (towerCoverMap k).left) ≫
          pullback.fst ((originalCovers).obj.obj k).hom coarseMap
    simp only [Category.assoc]
    rw [hp, ← Category.assoc,
      cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst,
      cmHarrisGeometricCoarseTowerPullbackCoverMap_fst]
    change (geometricSchemes).map (smallCMInclusion D _) ≫
        (geometricSchemes).map (smallCMInclusion D _) =
      (geometricSchemes).map (smallCMInclusion D _) ≫
        (geometricSchemes).map (smallCMInclusion D _)
    rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
      smallCMInclusion_trans, smallCMInclusion_trans]
  · have hp := etaleTorsorPullbackFunctor_map_snd coarseMap (pairOriginalActionMap k)
    change ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k)).left ≫
      pullback.snd ((originalCovers).obj.obj k).hom coarseMap =
        pullback.snd ((pairCovers).obj.obj k).hom coarseMap at hp
    change ((upperCoverMap k).left ≫
        ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k)).left) ≫
          pullback.snd ((originalCovers).obj.obj k).hom coarseMap =
      ((originalCoverMap k).left ≫ (towerCoverMap k).left) ≫
          pullback.snd ((originalCovers).obj.obj k).hom coarseMap
    simp only [Category.assoc]
    rw [hp, cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd,
      cmHarrisGeometricCoarseTowerPullbackCoverMap_snd]
    exact (originalCoverMap k).w.symm

/-- The coefficient identification is identity, so the upper comparison changes only the cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalRestrictedCoverIso_inclusion (k : ℕᵒᵖ) :
    (((upperCoverIso).hom.app pairOriginalCoefficients) ≫
      (association).map (originalCoefficientIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledPairCovers).action k) ((pairOriginalCoefficients).action k) ≫
        coverPullback J (upperCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((pairOriginalCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (originalCoefficientIso).hom)
  change ((association).map (originalCoefficientIso).hom).app k ≫ commonInc k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOriginalCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOriginalCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOriginalCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((upperCoverIso).hom.app pairOriginalCoefficients).app k ≫
      ((association).map (originalCoefficientIso).hom).app k) ≫ commonInc k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R upperGroupMap commonCovers
    pulledPairCovers upperDiagramMap k pairOriginalCoefficients

/-- The pulled original coarse comparison followed by the upper comparison pulls the composite cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    ((pulledOriginalIso).hom.app originalCoefficients ≫
        (upperCoverIso).hom.app pairOriginalCoefficients ≫
        (association).map (originalCoefficientIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
        coverPullback J
          (upperCoverMap k ≫ (etaleObjectPullback coarseMap).map (pairOriginalCoverMap k))
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) := by
  change (((pulledOriginalIso).hom.app originalCoefficients).app k ≫
      (((upperCoverIso).hom.app pairOriginalCoefficients).app k ≫
        ((association).map (originalCoefficientIso).hom).app k)) ≫ commonInc k = _
  have hu := cmHarrisGeometricUpperPairOriginalRestrictedCoverIso_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
    ρ p m hm existence geometry hRigid hRigidV k
  change (((upperCoverIso).hom.app pairOriginalCoefficients).app k ≫
      ((association).map (originalCoefficientIso).hom).app k) ≫ commonInc k = _ at hu
  have hp := etaleAssociatedAtGroupCoverChange_inclusion XT R originalGroupMap
    pulledPairCovers pulledOriginalCovers pulledOriginalMap k originalCoefficients
  change (((pulledOriginalIso).hom.app originalCoefficients).app k) ≫
      etaleAssociatedInclusion XT ((pulledPairCovers).action k) ((pairOriginalCoefficients).action k) =
    etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
      coverPullback J ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k))
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) at hp
  rw [Category.assoc, hu, ← Category.assoc, hp]
  change
    (etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
        coverPullback J ((etaleObjectPullback coarseMap).map (pairOriginalCoverMap k))
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k))) ≫
        coverPullback J (upperCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) = _
  rw [Category.assoc, ← coverPullback_comp]

/-- The original coarse and triple upper comparisons pull their actual composite cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalCoarseCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    ((towerCoverIso).hom ≫ (tripleUpperIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
        coverPullback J (originalCoverMap k ≫ towerCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) := by
  change ((towerCoverIso).hom.app k ≫ (tripleUpperIso).hom.app k) ≫ commonInc k = _
  rw [Category.assoc, cmHarrisGeometricTripleUpperCoverIso_inclusion, ← Category.assoc]
  have hm' := cmHarrisGeometricCoarseTowerCoverIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
    ρ p m hm existence geometry hRigid hRigidV k
  change (towerCoverIso).hom.app k ≫
      etaleAssociatedInclusion XT ((coarseCovers).action k) ((coarseCoefficients).action k) =
    etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
      coverPullback J (towerCoverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) at hm'
  rw [hm']
  change
    (etaleAssociatedInclusion XT ((pulledOriginalCovers).action k) ((originalCoefficients).action k) ≫
        coverPullback J (towerCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k))) ≫
        coverPullback J (originalCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((originalCoefficients).obj.obj k)) = _
  rw [Category.assoc, ← coverPullback_comp]

/-- The two full cover-change routes agree before the genuine inverse-image endpoint. -/
theorem cmHarrisGeometricUpperPairOriginalCoverIso_factorization :
    (pulledOriginalIso).hom.app originalCoefficients ≫
        (upperCoverIso).hom.app pairOriginalCoefficients ≫
        (association).map (originalCoefficientIso).hom =
      (towerCoverIso).hom ≫ (tripleUpperIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc k)).1
  rw [cmHarrisGeometricUpperPairOriginalCoverIso_hom_inclusion,
    cmHarrisGeometricUpperPairOriginalCoarseCoverIso_hom_inclusion,
    cmHarrisGeometricUpperPairOriginalPullbackCover_comp]

/-- The original coefficient upper-pair inverse-image route is the direct coarse-tower route to the upper vertex. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOriginalInverseIso_factorization :
    (pullSystems).map (pairOriginalIso).hom ≫ (originalInverseIso).hom =
      (towerInverseIso).hom ≫ (tripleUpperIso).hom := by
  change (pullSystems).map (pairOriginalIso).hom ≫
      (((inversePairOriginal).hom ≫ (upperCoverIso).hom.app pairOriginalCoefficients) ≫
        (association).map (originalCoefficientIso).hom) =
    ((inverseOriginal).hom ≫ (towerCoverIso).hom) ≫ (tripleUpperIso).hom
  simp only [Category.assoc]
  rw [← Category.assoc ((pullSystems).map (pairOriginalIso).hom),
    cmHarrisGeometricUpperPairOriginalCover_inverseImage, Category.assoc,
    cmHarrisGeometricUpperPairOriginalCoverIso_factorization]

/-- The constructed original coefficient endpoint equals the constructed coarse-tower inverse-image isomorphism for (U,V,T). -/
theorem cmHarrisGeometricTripleUpperPairOriginalSeparateInverseIso_eq_tower :
    originalSeparateIso = towerInverseIso := by
  apply Iso.ext
  change ((pullSystems).map (pairOriginalIso).hom ≫ (originalInverseIso).hom) ≫
      (tripleUpperIso).inv = (towerInverseIso).hom
  rw [cmHarrisGeometricUpperPairOriginalInverseIso_factorization,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
