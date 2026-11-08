import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseTower
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseInverseImage
import Langlands.Shimura.Coefficients.EtaleInverseImageConstantProduct

/-! # Composition of actual inverse image along the original coarse CM tower -/

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

variable (hRigidU : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "XU" => (geometricSchemes).obj U
local notation "mapVU" => (geometricSchemes).map (smallCMInclusion D hVU)
local notation "mapTU" => (geometricSchemes).map (smallCMInclusion D hTU)
local notation "originalCoefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "originalCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigidU
local notation "originalSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigidU
local notation "originalInc" k:arg => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigidU k
local notation "directV" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU
local notation "directT" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU
local notation "directCoverV" k:arg => cmHarrisGeometricCoarsePullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU k
local notation "directCoverT" k:arg => cmHarrisGeometricCoarsePullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU k
local notation "towerCover" k:arg => cmHarrisGeometricCoarseTowerPullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k
local notation "towerInverseIso" => cmHarrisGeometricCoarseTowerInverseIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV
local notation "pairInc" k:arg => cmHarrisGeometricCoarseAssociatedInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV k

omit [Module.Finite ℚ A] in
/-- The literal geometric coarse arrows compose by functoriality of the represented tower. -/
theorem cmHarrisGeometricCoarseTowerBaseMap_comp :
    coarseMap ≫ mapVU = mapTU := by
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

local notation "baseEq" => cmHarrisGeometricCoarseTowerBaseMap_comp D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV

/-- The actual intersection-cover maps agree through the literal single-to-iterated
pullback comparison and equality transport of the represented coarse arrow. -/
theorem cmHarrisGeometricCoarseTowerCover_comp (k : ℕᵒᵖ) :
    directCoverT k ≫
        (etaleObjectPullbackCongr baseEq).inv.app ((originalCovers).obj.obj k) ≫
        (etaleObjectPullbackComp mapVU coarseMap).hom.app ((originalCovers).obj.obj k) =
      towerCover k ≫ (etaleObjectPullback coarseMap).map (directCoverV k) := by
  let O : (XU).Etale := (originalCovers).obj.obj k
  let a := (directCoverT k).left
  let c := ((etaleObjectPullbackCongr baseEq).inv.app O).left
  let d := ((etaleObjectPullbackComp mapVU coarseMap).hom.app O).left
  let b := (towerCover k).left
  let e := ((etaleObjectPullback coarseMap).map (directCoverV k)).left
  have cf : c ≫ pullback.fst O.hom (coarseMap ≫ mapVU) =
      pullback.fst O.hom mapTU := by
    dsimp only [c, etaleObjectPullbackCongr, MorphismProperty.Over.pullbackCongr]
    simp
  have cs : c ≫ pullback.snd O.hom (coarseMap ≫ mapVU) =
      pullback.snd O.hom mapTU :=
    ((etaleObjectPullbackCongr baseEq).inv.app O).w
  have dff : d ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
      pullback.fst O.hom mapVU = pullback.fst O.hom (coarseMap ≫ mapVU) :=
    etaleObjectPullbackComp_hom_fst_fst mapVU coarseMap O
  have dfs : d ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
      pullback.snd O.hom mapVU =
      pullback.snd O.hom (coarseMap ≫ mapVU) ≫ coarseMap :=
    etaleObjectPullbackComp_hom_fst_snd mapVU coarseMap O
  have ds : d ≫ pullback.snd (pullback.snd O.hom mapVU) coarseMap =
      pullback.snd O.hom (coarseMap ≫ mapVU) :=
    etaleObjectPullbackComp_hom_snd mapVU coarseMap O
  have ef : e ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap =
      pullback.fst ((pairCovers).obj.obj k).hom coarseMap ≫ (directCoverV k).left :=
    etaleObjectPullback_map_fst coarseMap (directCoverV k)
  have es : e ≫ pullback.snd (pullback.snd O.hom mapVU) coarseMap =
      pullback.snd ((pairCovers).obj.obj k).hom coarseMap :=
    etaleObjectPullback_map_snd coarseMap (directCoverV k)
  apply MorphismProperty.Over.Hom.ext
  change a ≫ c ≫ d = b ≫ e
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change (a ≫ c ≫ d) ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
          pullback.fst O.hom mapVU =
        (b ≫ e) ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
          pullback.fst O.hom mapVU
      simp only [Category.assoc, dff, cf, reassoc_of% ef]
      dsimp only [a, b]
      rw [cmHarrisGeometricCoarsePullbackCoverMap_fst,
        cmHarrisGeometricCoarseTowerPullbackCoverMap_fst_assoc,
        cmHarrisGeometricCoarsePullbackCoverMap_fst]
      change (geometricSchemes).map (smallCMInclusion D _) =
        (geometricSchemes).map (smallCMInclusion D _) ≫
          (geometricSchemes).map (smallCMInclusion D _)
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]
    · change (a ≫ c ≫ d) ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
          pullback.snd O.hom mapVU =
        (b ≫ e) ≫ pullback.fst (pullback.snd O.hom mapVU) coarseMap ≫
          pullback.snd O.hom mapVU
      simp only [Category.assoc, dfs, reassoc_of% cs, reassoc_of% ef]
      dsimp only [a, b]
      rw [cmHarrisGeometricCoarsePullbackCoverMap_snd_assoc,
        cmHarrisGeometricCoarseTowerPullbackCoverMap_fst_assoc,
        cmHarrisGeometricCoarsePullbackCoverMap_snd]
      exact (cmHarrisGeometricCoarseTowerFineMap_projection D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k).symm
  · change (a ≫ c ≫ d) ≫ pullback.snd (pullback.snd O.hom mapVU) coarseMap =
      (b ≫ e) ≫ pullback.snd (pullback.snd O.hom mapVU) coarseMap
    simp only [Category.assoc, ds, cs, es]
    exact (cmHarrisGeometricCoarsePullbackCoverMap_snd D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU k).trans
      (cmHarrisGeometricCoarseTowerPullbackCoverMap_snd D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k).symm

local notation "modAt" k:arg => (originalCoefficients).obj.obj k
local notation "constantU" k:arg => (constantSheaf (Scheme.smallEtaleTopology XU) (ModuleCat.{0} R)).obj (modAt k)
local notation "constantV" k:arg => (constantSheaf (Scheme.smallEtaleTopology XV) (ModuleCat.{0} R)).obj (modAt k)
local notation "constantT" k:arg => (constantSheaf J (ModuleCat.{0} R)).obj (modAt k)
local notation "originalProduct" k:arg => (productSheaf (Scheme.smallEtaleTopology XU) ((originalCovers).obj.obj k)).obj (constantU k)
local notation "congrCover" k:arg => (etaleObjectPullbackCongr baseEq).app ((originalCovers).obj.obj k)
local notation "compCover" k:arg => (etaleObjectPullbackComp mapVU coarseMap).app ((originalCovers).obj.obj k)

/-- In constant product coordinates the direct and successive original-cover
routes coincide, retaining both actual inverse-image comparison morphisms. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerConstantProduct_comp (k : ℕᵒᵖ) :
    (inverseImageComp R mapVU coarseMap).hom.app (originalProduct k) ≫
      (inverseImageCongr R baseEq).hom.app (originalProduct k) ≫
      inverseImageConstantProductMap mapTU R ((originalCovers).obj.obj k) (modAt k) ≫
      coverPullback J (directCoverT k) (constantT k) =
    (inverseImage coarseMap R).map
        (inverseImageConstantProductMap mapVU R ((originalCovers).obj.obj k) (modAt k) ≫
          coverPullback (Scheme.smallEtaleTopology XV) (directCoverV k) (constantV k)) ≫
      inverseImageConstantProductMap coarseMap R ((pairCovers).obj.obj k) (modAt k) ≫
      coverPullback J (towerCover k) (constantT k) := by
  have hc : coverPullback J (congrCover k).hom (constantT k) ≫
      coverPullback J (congrCover k).inv (constantT k) = 𝟙 _ := by
    rw [← coverPullback_comp, Iso.inv_hom_id, coverPullback_id]
  have he : (inverseImageCongr R baseEq).hom.app (originalProduct k) ≫
        inverseImageConstantProductMap mapTU R ((originalCovers).obj.obj k) (modAt k) ≫
        coverPullback J (directCoverT k) (constantT k) =
      inverseImageConstantProductMap (coarseMap ≫ mapVU) R
          ((originalCovers).obj.obj k) (modAt k) ≫
        coverPullback J (congrCover k).inv (constantT k) ≫
        coverPullback J (directCoverT k) (constantT k) := by
    calc
      _ = (inverseImageCongr R baseEq).hom.app (originalProduct k) ≫
          inverseImageConstantProductMap mapTU R ((originalCovers).obj.obj k) (modAt k) ≫
          (coverPullback J (congrCover k).hom (constantT k) ≫
            coverPullback J (congrCover k).inv (constantT k)) ≫
          coverPullback J (directCoverT k) (constantT k) := by
        rw [hc, Category.id_comp]
      _ = _ := by
        simpa only [Category.assoc, Iso.app_hom, Iso.app_inv] using congrArg
          (fun a => a ≫ coverPullback J (congrCover k).inv (constantT k) ≫
            coverPullback J (directCoverT k) (constantT k))
          (inverseImageConstantProductMap_congr (coarseMap ≫ mapVU) R baseEq
            ((originalCovers).obj.obj k) (modAt k))
  rw [he, inverseImageConstantProductMap_comp_assoc]
  calc
    _ = (inverseImage coarseMap R).map
          (inverseImageConstantProductMap mapVU R ((originalCovers).obj.obj k) (modAt k)) ≫
        inverseImageConstantProductMap coarseMap R
          ((etaleObjectPullback mapVU).obj ((originalCovers).obj.obj k)) (modAt k) ≫
        coverPullback J (directCoverT k ≫ (congrCover k).inv ≫ (compCover k).hom)
          (constantT k) := by
      simp only [coverPullback_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
    _ = (inverseImage coarseMap R).map
          (inverseImageConstantProductMap mapVU R ((originalCovers).obj.obj k) (modAt k)) ≫
        inverseImageConstantProductMap coarseMap R
          ((etaleObjectPullback mapVU).obj ((originalCovers).obj.obj k)) (modAt k) ≫
        coverPullback J (towerCover k ≫ (etaleObjectPullback coarseMap).map (directCoverV k))
          (constantT k) := by
      simp only [Iso.app_hom, Iso.app_inv]
      rw [cmHarrisGeometricCoarseTowerCover_comp]
    _ = _ := by
      rw [coverPullback_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [inverseImageConstantProductMap_coverPullback_assoc]
      rfl

/-- The direct comparison at V in constant-product coordinates. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerDirectV_hom_inclusion (k : ℕᵒᵖ) :
    (directV).hom.app k ≫ pairInc k =
      (inverseImage mapVU R).map (originalInc k) ≫
        inverseImageConstantProductMap mapVU R ((originalCovers).obj.obj k) (modAt k) ≫
        coverPullback (Scheme.smallEtaleTopology XV) (directCoverV k) (constantV k) := by
  rw [cmHarrisGeometricCoarseInverseImageAssociatedIso_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU k]
  simp only [inverseImageConstantProductMap, inverseImageProductSheafIso_hom,
    Category.assoc]
  rfl

/-- The direct comparison at T in constant-product coordinates. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerDirectT_hom_inclusion (k : ℕᵒᵖ) :
    (directT).hom.app k ≫ commonInc k =
      (inverseImage mapTU R).map (originalInc k) ≫
        inverseImageConstantProductMap mapTU R ((originalCovers).obj.obj k) (modAt k) ≫
        coverPullback J (directCoverT k) (constantT k) := by
  rw [cmHarrisGeometricCoarseInverseImageAssociatedIso_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid hRigidU k]
  simp only [inverseImageConstantProductMap, inverseImageProductSheafIso_hom,
    Category.assoc]
  rfl

/-- The tower comparison in the same unchanged original constant coefficients. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerStep_hom_inclusion (k : ℕᵒᵖ) :
    (towerInverseIso).hom.app k ≫ commonInc k =
      (inverseImage coarseMap R).map (pairInc k) ≫
        inverseImageConstantProductMap coarseMap R ((pairCovers).obj.obj k) (modAt k) ≫
        coverPullback J (towerCover k) (constantT k) := by
  rw [cmHarrisGeometricCoarseTowerInverseIso_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k]
  simp only [inverseImageConstantProductMap, inverseImageProductSheafIso_hom,
    Category.assoc]
  rfl

/-- Successive inverse image, first to V and then to T, on the full original system. -/
def cmHarrisGeometricCoarseTowerIteratedIso :
    (originalSystem ⋙ inverseImage mapVU R) ⋙ inverseImage coarseMap R ≅ systemT :=
  Functor.isoWhiskerRight directV (inverseImage coarseMap R) ≪≫ towerInverseIso

/-- The direct comparison after actual composition and equality transport of inverse image. -/
def cmHarrisGeometricCoarseTowerDirectIso :
    (originalSystem ⋙ inverseImage mapVU R) ⋙ inverseImage coarseMap R ≅ systemT :=
  Functor.associator originalSystem (inverseImage mapVU R) (inverseImage coarseMap R) ≪≫
    Functor.isoWhiskerLeft originalSystem
      (inverseImageComp R mapVU coarseMap ≪≫ inverseImageCongr R baseEq) ≪≫ directT

local notation "iteratedIso" => cmHarrisGeometricCoarseTowerIteratedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU
local notation "directIso" => cmHarrisGeometricCoarseTowerDirectIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidU

/-- The two actual inverse-image routes agree on every original coefficient sheaf. -/
@[reassoc] theorem cmHarrisGeometricCoarseTowerInverseImage_hom_comp (k : ℕᵒᵖ) :
    (inverseImageComp R mapVU coarseMap).hom.app ((originalSystem).obj k) ≫
      (inverseImageCongr R baseEq).hom.app ((originalSystem).obj k) ≫
      (directT).hom.app k =
    (inverseImage coarseMap R).map ((directV).hom.app k) ≫
      (towerInverseIso).hom.app k := by
  apply (cancel_mono (commonInc k)).1
  simp only [Category.assoc]
  rw [cmHarrisGeometricCoarseTowerDirectT_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidU k,
    cmHarrisGeometricCoarseTowerStep_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV k]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rw [cmHarrisGeometricCoarseTowerConstantProduct_comp D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU k]
  rw [← Functor.map_comp_assoc,
    cmHarrisGeometricCoarseTowerDirectV_hom_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V hVU ρ p m hm existence geometry hRigidV hRigidU k,
    Functor.map_comp, Functor.map_comp]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

/-- Direct and successive coarse inverse image are equal as full-system isomorphisms. -/
theorem cmHarrisGeometricCoarseTowerIteratedIso_eq : iteratedIso = directIso := by
  apply Iso.ext
  apply NatTrans.ext
  funext k
  change (inverseImage coarseMap R).map ((directV).hom.app k) ≫
      (towerInverseIso).hom.app k =
    𝟙 _ ≫ ((inverseImageComp R mapVU coarseMap).hom.app ((originalSystem).obj k) ≫
      (inverseImageCongr R baseEq).hom.app ((originalSystem).obj k)) ≫
      (directT).hom.app k
  simpa only [Category.id_comp, Category.assoc] using
    (cmHarrisGeometricCoarseTowerInverseImage_hom_comp D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid hRigidV hRigidU k).symm

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
