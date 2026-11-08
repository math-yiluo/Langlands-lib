import Langlands.Shimura.PEL.HarrisTaylorCMGeometricUpperPairCoherence
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseInverseImage
import Langlands.Shimura.Coefficients.EtaleInverseImageGroupCoverChange

/-! # Normalization of the original upper-pair own inverse-image endpoint -/

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

local notation "XT" => (geometricSchemes).obj T
local notation "XV" => (geometricSchemes).obj V
local notation "J" => Scheme.smallEtaleTopology XT
local notation "R" => HarrisCoefficientIntegers K p
local notation "coarseMap" => (geometricSchemes).map (smallCMInclusion D hTV)
local notation "pullSystems" => (Functor.whiskeringRight ℕᵒᵖ _ _).obj (inverseImage coarseMap R)
local notation "association" => cmHarrisGeometricTripleCommonAssociation D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleMiddleIso" => cmHarrisGeometricTripleMiddleCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "pairOwnIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "ownInverseIso" => cmHarrisGeometricTripleUpperPairOwnInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

local notation "pairGroups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "pairCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pairProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "ownGroups" => cmHarrisCoefficientGroups D ρ p V m hm
local notation "ownGroupMap" => cmHarrisLatticeCommonOwnGroupMap D ρ p U V hVU m hm
local notation "ownCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V ρ p m hm existence geometry hRigidV
local notation "ownProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V ρ p m hm existence geometry hRigidV
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p V m hm
local notation "pairOwnCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "pairOwnCoverMap" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k
local notation "pairOwnActionMap" k:arg => cmHarrisGeometricLatticeCommonOwnActionMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k
local notation "commonCovers" => cmHarrisGeometricTripleCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricTripleCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "commonInc" k:arg => cmHarrisGeometricTripleCommonSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid 1 k
local notation "upperGroupMap" => cmHarrisTripleUpperPairGroupMap D ρ p U V T hVU hTV m hm
local notation "upperCoverMap" k:arg => cmHarrisGeometricTripleUpperPairPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k
local notation "upperDiagramMap" => cmHarrisGeometricTripleUpperPairPullbackDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "ownCoefficientIso" => cmHarrisTripleUpperPairOwnCoefficientIso D ρ p U V T hVU hTV m hm
local notation "middleCoverMap" k:arg => cmHarrisGeometricTripleMiddleCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "middleCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p V T hTV m hm
local notation "middleCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "coarseCoverMap" k:arg => cmHarrisGeometricCoarsePullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid hRigidV k
local notation "coarseCoverIso" => cmHarrisGeometricCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid hRigidV
local notation "coarseInverseIso" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid hRigidV
local notation "ownSeparateIso" => cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV

/-- Package the original own-cover map and every original exponent transition. -/
def cmHarrisGeometricUpperPairOwnCoverDiagramMap :
    pairCovers ⟶ (EquivariantDiagram.groupRestriction (XV).Etale ownGroupMap).obj ownCovers where
  hom :=
    { app k := pairOwnCoverMap k
      naturality _ _ f := cmHarrisGeometricLatticeCommonOwnCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV f }
  comm k g := (pairOwnActionMap k).comm g

local notation "ownDiagramMap" => cmHarrisGeometricUpperPairOwnCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV
local notation "pulledPairCovers" => (etaleTorsorDiagramPullback coarseMap pairGroups).obj pairCovers
local notation "pulledOwnCovers" => (etaleTorsorDiagramPullback coarseMap ownGroups).obj ownCovers
local notation "pulledPairProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor coarseMap pairGroups pairCovers pairProperty
local notation "pulledOwnProperty" => etaleTorsorDiagramPullback_isFiniteGeometricTorsor coarseMap ownGroups ownCovers ownProperty
local notation "pulledOwnMap" => etaleGroupCoverMapPullback coarseMap ownGroupMap pairCovers ownCovers ownDiagramMap
local notation "pulledOwnIso" => etaleAssociatedVaryingGroupCoverIso XT R ownGroupMap pulledPairCovers pulledOwnCovers pulledOwnMap pulledPairProperty pulledOwnProperty
local notation "upperCoverIso" => etaleAssociatedVaryingGroupCoverIso XT R upperGroupMap commonCovers pulledPairCovers upperDiagramMap commonProperty pulledPairProperty
local notation "inverseOwn" => (etaleAssociatedVaryingSystemInverseImage coarseMap R ownCovers ownProperty).app ownCoefficients
local notation "inversePairOwn" => (etaleAssociatedVaryingSystemInverseImage coarseMap R pairCovers pairProperty).app pairOwnCoefficients

/-- The original own-cover system isomorphism satisfies the generic genuine inverse-image square. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnCover_inverseImage :
    (pullSystems).map (pairOwnIso).hom ≫ (inversePairOwn).hom =
      (inverseOwn).hom ≫ (pulledOwnIso).hom.app ownCoefficients :=
  etaleAssociatedVaryingGroupCoverIso_inverseImage_hom coarseMap R ownGroupMap
    pairCovers ownCovers ownDiagramMap pairProperty ownProperty ownCoefficients

/-- The two actual routes into the same pulled own cover agree. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnPullbackCover_comp (k : ℕᵒᵖ) :
    upperCoverMap k ≫ (etaleObjectPullback coarseMap).map (pairOwnCoverMap k) =
      middleCoverMap k ≫ coarseCoverMap k := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · have hp := etaleTorsorPullbackFunctor_map_fst coarseMap (pairOwnActionMap k)
    change ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k)).left ≫
      pullback.fst ((ownCovers).obj.obj k).hom coarseMap =
        pullback.fst ((pairCovers).obj.obj k).hom coarseMap ≫
          (pairOwnCoverMap k).left at hp
    change ((upperCoverMap k).left ≫
        ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k)).left) ≫
          pullback.fst ((ownCovers).obj.obj k).hom coarseMap =
      ((middleCoverMap k).left ≫ (coarseCoverMap k).left) ≫
          pullback.fst ((ownCovers).obj.obj k).hom coarseMap
    simp only [Category.assoc]
    rw [hp, ← Category.assoc,
      cmHarrisGeometricTripleUpperPairPullbackCoverMap_fst,
      cmHarrisGeometricCoarsePullbackCoverMap_fst]
    change (geometricSchemes).map (smallCMInclusion D _) ≫
        (geometricSchemes).map (smallCMInclusion D _) =
      (geometricSchemes).map (smallCMInclusion D _) ≫
        (geometricSchemes).map (smallCMInclusion D _)
    rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
      smallCMInclusion_trans, smallCMInclusion_trans]
  · have hp := etaleTorsorPullbackFunctor_map_snd coarseMap (pairOwnActionMap k)
    change ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k)).left ≫
      pullback.snd ((ownCovers).obj.obj k).hom coarseMap =
        pullback.snd ((pairCovers).obj.obj k).hom coarseMap at hp
    change ((upperCoverMap k).left ≫
        ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k)).left) ≫
          pullback.snd ((ownCovers).obj.obj k).hom coarseMap =
      ((middleCoverMap k).left ≫ (coarseCoverMap k).left) ≫
          pullback.snd ((ownCovers).obj.obj k).hom coarseMap
    simp only [Category.assoc]
    rw [hp, cmHarrisGeometricTripleUpperPairPullbackCoverMap_snd,
      cmHarrisGeometricCoarsePullbackCoverMap_snd]
    exact (middleCoverMap k).w.symm

/-- The coefficient identification is identity, so the upper comparison changes only the cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnRestrictedCoverIso_inclusion (k : ℕᵒᵖ) :
    (((upperCoverIso).hom.app pairOwnCoefficients) ≫
      (association).map (ownCoefficientIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledPairCovers).action k) ((pairOwnCoefficients).action k) ≫
        coverPullback J (upperCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((pairOwnCoefficients).obj.obj k)) := by
  have hc := etaleAssociatedInclusion_natural XT ((commonCovers).action k)
    ((EquivariantDiagram.evaluation k).map (ownCoefficientIso).hom)
  change ((association).map (ownCoefficientIso).hom).app k ≫ commonInc k =
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOwnCoefficients).action k) ≫
      (productSheaf J ((commonCovers).obj.obj k)).map
        ((constantSheaf J (ModuleCat.{0} R)).map (𝟙 _)) at hc
  have hp := congrArg (fun a => (productSheaf J ((commonCovers).obj.obj k)).map a)
    ((constantSheaf J (ModuleCat.{0} R)).map_id
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOwnCoefficients).action k).V)
  have hp' := hp.trans ((productSheaf J ((commonCovers).obj.obj k)).map_id _)
  have hc' := hc.trans ((congrArg (fun a =>
    etaleAssociatedInclusion XT ((commonCovers).action k)
      (((EquivariantDiagram.groupRestriction (ModuleCat.{0} R) upperGroupMap).obj
        pairOwnCoefficients).action k) ≫ a) hp').trans (Category.comp_id _))
  change (((upperCoverIso).hom.app pairOwnCoefficients).app k ≫
      ((association).map (ownCoefficientIso).hom).app k) ≫ commonInc k = _
  rw [Category.assoc, hc']
  exact etaleAssociatedAtGroupCoverChange_inclusion XT R upperGroupMap commonCovers
    pulledPairCovers upperDiagramMap k pairOwnCoefficients

/-- The pulled original own comparison followed by the upper comparison pulls the composite cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    ((pulledOwnIso).hom.app ownCoefficients ≫
        (upperCoverIso).hom.app pairOwnCoefficients ≫
        (association).map (ownCoefficientIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J
          (upperCoverMap k ≫ (etaleObjectPullback coarseMap).map (pairOwnCoverMap k))
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) := by
  change (((pulledOwnIso).hom.app ownCoefficients).app k ≫
      (((upperCoverIso).hom.app pairOwnCoefficients).app k ≫
        ((association).map (ownCoefficientIso).hom).app k)) ≫ commonInc k = _
  have hu := cmHarrisGeometricUpperPairOwnRestrictedCoverIso_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
    ρ p m hm existence geometry hRigid hRigidV k
  change (((upperCoverIso).hom.app pairOwnCoefficients).app k ≫
      ((association).map (ownCoefficientIso).hom).app k) ≫ commonInc k = _ at hu
  have hp := etaleAssociatedAtGroupCoverChange_inclusion XT R ownGroupMap
    pulledPairCovers pulledOwnCovers pulledOwnMap k ownCoefficients
  change (((pulledOwnIso).hom.app ownCoefficients).app k) ≫
      etaleAssociatedInclusion XT ((pulledPairCovers).action k) ((pairOwnCoefficients).action k) =
    etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
      coverPullback J ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k))
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) at hp
  rw [Category.assoc, hu, ← Category.assoc, hp]
  change
    (etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J ((etaleObjectPullback coarseMap).map (pairOwnCoverMap k))
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k))) ≫
        coverPullback J (upperCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) = _
  rw [Category.assoc, ← coverPullback_comp]

/-- The original coarse and triple middle comparisons pull their actual composite cover. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnCoarseCoverIso_hom_inclusion (k : ℕᵒᵖ) :
    ((coarseCoverIso).hom ≫ (tripleMiddleIso).hom).app k ≫ commonInc k =
      etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J (middleCoverMap k ≫ coarseCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) := by
  change ((coarseCoverIso).hom.app k ≫ (tripleMiddleIso).hom.app k) ≫ commonInc k = _
  rw [Category.assoc, cmHarrisGeometricTripleMiddleCoverIso_inclusion, ← Category.assoc]
  have hm' := cmHarrisGeometricCoarseAssociatedCoverIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q V T hTV
    ρ p m hm existence geometry hRigid hRigidV k
  change (coarseCoverIso).hom.app k ≫
      etaleAssociatedInclusion XT ((middleCovers).action k) ((middleCoefficients).action k) =
    etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
      coverPullback J (coarseCoverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) at hm'
  rw [hm']
  change
    (etaleAssociatedInclusion XT ((pulledOwnCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J (coarseCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k))) ≫
        coverPullback J (middleCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) = _
  rw [Category.assoc, ← coverPullback_comp]

/-- The two full cover-change routes agree before the genuine inverse-image endpoint. -/
theorem cmHarrisGeometricUpperPairOwnCoverIso_factorization :
    (pulledOwnIso).hom.app ownCoefficients ≫
        (upperCoverIso).hom.app pairOwnCoefficients ≫
        (association).map (ownCoefficientIso).hom =
      (coarseCoverIso).hom ≫ (tripleMiddleIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc k)).1
  rw [cmHarrisGeometricUpperPairOwnCoverIso_hom_inclusion,
    cmHarrisGeometricUpperPairOwnCoarseCoverIso_hom_inclusion,
    cmHarrisGeometricUpperPairOwnPullbackCover_comp]

/-- The original upper-pair own inverse-image route is the direct coarse route to the middle vertex. -/
@[reassoc] theorem cmHarrisGeometricUpperPairOwnInverseIso_factorization :
    (pullSystems).map (pairOwnIso).hom ≫ (ownInverseIso).hom =
      (coarseInverseIso).hom ≫ (tripleMiddleIso).hom := by
  change (pullSystems).map (pairOwnIso).hom ≫
      (((inversePairOwn).hom ≫ (upperCoverIso).hom.app pairOwnCoefficients) ≫
        (association).map (ownCoefficientIso).hom) =
    ((inverseOwn).hom ≫ (coarseCoverIso).hom) ≫ (tripleMiddleIso).hom
  simp only [Category.assoc]
  rw [← Category.assoc ((pullSystems).map (pairOwnIso).hom),
    cmHarrisGeometricUpperPairOwnCover_inverseImage, Category.assoc,
    cmHarrisGeometricUpperPairOwnCoverIso_factorization]

/-- The constructed own endpoint equals the existing coarse inverse-image isomorphism for (V,T). -/
theorem cmHarrisGeometricTripleUpperPairOwnSeparateInverseIso_eq_coarse :
    ownSeparateIso = coarseInverseIso := by
  apply Iso.ext
  change ((pullSystems).map (pairOwnIso).hom ≫ (ownInverseIso).hom) ≫
      (tripleMiddleIso).inv = (coarseInverseIso).hom
  rw [cmHarrisGeometricUpperPairOwnInverseIso_factorization,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
