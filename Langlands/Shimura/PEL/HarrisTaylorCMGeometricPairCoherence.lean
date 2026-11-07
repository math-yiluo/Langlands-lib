import Langlands.Shimura.PEL.HarrisTaylorCMGeometricPairTriple
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricTripleSeparate
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeCoverComparison

/-! # Original pair maps and geometric triple refinement coherence -/

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

local notation "tripleOwnIso" => cmHarrisGeometricTripleOwnCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleOwnCover" k:arg => cmHarrisGeometricTripleOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "tripleMiddleIso" => cmHarrisGeometricTripleMiddleCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleMiddleCover" k:arg => cmHarrisGeometricTripleMiddleCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "tripleUpperIso" => cmHarrisGeometricTripleUpperCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "tripleUpperCover" k:arg => cmHarrisGeometricTripleUpperCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "separateChain" => cmHarrisGeometricTripleSeparateSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

local notation "directPairOwnIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directOwnIso" => cmHarrisGeometricTripleDirectPairOwnSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "directOwnCover" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid k
local notation "directPairOriginalIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directOriginalIso" => cmHarrisGeometricTripleDirectPairOriginalSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "directOriginalCover" k:arg => cmHarrisGeometricLatticeCommonCoarseCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid k
local notation "directPairCover" k:arg => cmHarrisGeometricTripleDirectPairCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "directPairInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid
local notation "directComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU ρ p m hm existence geometry hRigid

/-- The two original forgetting maps compose to the original triple forgetting map. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOwnCoverMap_comp (k : ℕᵒᵖ) :
    directPairCover k ≫ directOwnCover k = tripleOwnCover k := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D (cmHarrisLatticeCommonLevel_le_own D ρ p U T hTU m hm k.unop)) =
    (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k.unop))
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

/-- Factoring through the original pair cover gives exactly the original triple cover comparison. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOwnSystemIso_factorization :
    (directPairOwnIso).hom ≫ (directOwnIso).hom = (tripleOwnIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc 0 k)).1
  change ((directPairOwnIso).hom.app k ≫ (directOwnIso).hom.app k) ≫ commonInc 0 k =
    (tripleOwnIso).hom.app k ≫ commonInc 0 k
  rw [Category.assoc, cmHarrisGeometricTripleDirectPairOwnSystemIso_inclusion,
    ← Category.assoc, cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso_hom_app,
    cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion,
    cmHarrisGeometricTripleOwnCoverIso_inclusion]
  let Fₖ := (constantSheaf J (ModuleCat.{0} R)).obj
    ((cmHarrisCoefficientDiagram D ρ p T m hm).obj.obj k)
  have hc : coverPullback J (directOwnCover k) Fₖ ≫
      coverPullback J (directPairCover k) Fₖ =
        coverPullback J (tripleOwnCover k) Fₖ := by
    rw [← coverPullback_comp,
      cmHarrisGeometricTripleDirectPairOwnCoverMap_comp]
  change (_ ≫ coverPullback J (directOwnCover k) Fₖ) ≫
      coverPullback J (directPairCover k) Fₖ =
    _ ≫ coverPullback J (tripleOwnCover k) Fₖ
  rw [Category.assoc, hc]

/-- The two original forgetting maps compose to the original triple forgetting map. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOriginalCoverMap_comp (k : ℕᵒᵖ) :
    directPairCover k ≫ directOriginalCover k = tripleUpperCover k := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_pair D ρ p U V T hVU hTV m hm k.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D (cmHarrisLatticeCommonLevel_le_coarse D ρ p U T hTU m hm k.unop)) =
    (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_upper D ρ p U V T hVU hTV m hm k.unop))
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

/-- Factoring through the original pair cover gives exactly the original triple cover comparison. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairOriginalSystemIso_factorization :
    (directPairOriginalIso).hom ≫ (directOriginalIso).hom = (tripleUpperIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc 2 k)).1
  change ((directPairOriginalIso).hom.app k ≫ (directOriginalIso).hom.app k) ≫ commonInc 2 k =
    (tripleUpperIso).hom.app k ≫ commonInc 2 k
  rw [Category.assoc, cmHarrisGeometricTripleDirectPairOriginalSystemIso_inclusion,
    ← Category.assoc, cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso_hom_app,
    cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion,
    cmHarrisGeometricTripleUpperCoverIso_inclusion]
  let Fₖ := (constantSheaf J (ModuleCat.{0} R)).obj
    ((cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm).obj.obj k)
  have hc : coverPullback J (directOriginalCover k) Fₖ ≫
      coverPullback J (directPairCover k) Fₖ =
        coverPullback J (tripleUpperCover k) Fₖ := by
    rw [← coverPullback_comp,
      cmHarrisGeometricTripleDirectPairOriginalCoverMap_comp]
  change (_ ≫ coverPullback J (directOriginalCover k) Fₖ) ≫
      coverPullback J (directPairCover k) Fₖ =
    _ ≫ coverPullback J (tripleUpperCover k) Fₖ
  rw [Category.assoc, hc]

local notation "lowerPairOwnIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerOwnIso" => cmHarrisGeometricTripleLowerPairOwnSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "lowerOwnCover" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid k
local notation "lowerPairOriginalIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerOriginalIso" => cmHarrisGeometricTripleLowerPairOriginalSystemIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid
local notation "lowerOriginalCover" k:arg => cmHarrisGeometricLatticeCommonCoarseCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid k
local notation "lowerPairCover" k:arg => cmHarrisGeometricTripleLowerPairCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k
local notation "lowerPairInclusion" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid
local notation "lowerComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV ρ p m hm existence geometry hRigid

/-- The two original forgetting maps compose to the original triple forgetting map. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOwnCoverMap_comp (k : ℕᵒᵖ) :
    lowerPairCover k ≫ lowerOwnCover k = tripleOwnCover k := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D (cmHarrisLatticeCommonLevel_le_own D ρ p V T hTV m hm k.unop)) =
    (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k.unop))
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

/-- Factoring through the original pair cover gives exactly the original triple cover comparison. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOwnSystemIso_factorization :
    (lowerPairOwnIso).hom ≫ (lowerOwnIso).hom = (tripleOwnIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc 0 k)).1
  change ((lowerPairOwnIso).hom.app k ≫ (lowerOwnIso).hom.app k) ≫ commonInc 0 k =
    (tripleOwnIso).hom.app k ≫ commonInc 0 k
  rw [Category.assoc, cmHarrisGeometricTripleLowerPairOwnSystemIso_inclusion,
    ← Category.assoc, cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso_hom_app,
    cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion,
    cmHarrisGeometricTripleOwnCoverIso_inclusion]
  let Fₖ := (constantSheaf J (ModuleCat.{0} R)).obj
    ((cmHarrisCoefficientDiagram D ρ p T m hm).obj.obj k)
  have hc : coverPullback J (lowerOwnCover k) Fₖ ≫
      coverPullback J (lowerPairCover k) Fₖ =
        coverPullback J (tripleOwnCover k) Fₖ := by
    rw [← coverPullback_comp,
      cmHarrisGeometricTripleLowerPairOwnCoverMap_comp]
  change (_ ≫ coverPullback J (lowerOwnCover k) Fₖ) ≫
      coverPullback J (lowerPairCover k) Fₖ =
    _ ≫ coverPullback J (tripleOwnCover k) Fₖ
  rw [Category.assoc, hc]

/-- The two original forgetting maps compose to the original triple forgetting map. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOriginalCoverMap_comp (k : ℕᵒᵖ) :
    lowerPairCover k ≫ lowerOriginalCover k = tripleMiddleCover k := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_lowerPair D ρ p U V T hVU hTV m hm k.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D (cmHarrisLatticeCommonLevel_le_coarse D ρ p V T hTV m hm k.unop)) =
    (geometricSchemes).map (smallCMInclusion D (cmHarrisTripleCommonLevel_le_middle D ρ p U V T hVU hTV m hm k.unop))
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

/-- Factoring through the original pair cover gives exactly the original triple cover comparison. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairOriginalSystemIso_factorization :
    (lowerPairOriginalIso).hom ≫ (lowerOriginalIso).hom = (tripleMiddleIso).hom := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono (commonInc 1 k)).1
  change ((lowerPairOriginalIso).hom.app k ≫ (lowerOriginalIso).hom.app k) ≫ commonInc 1 k =
    (tripleMiddleIso).hom.app k ≫ commonInc 1 k
  rw [Category.assoc, cmHarrisGeometricTripleLowerPairOriginalSystemIso_inclusion,
    ← Category.assoc, cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso_hom_app,
    cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion,
    cmHarrisGeometricTripleMiddleCoverIso_inclusion]
  let Fₖ := (constantSheaf J (ModuleCat.{0} R)).obj
    ((cmHarrisCoarseCoefficientDiagram D ρ p V T hTV m hm).obj.obj k)
  have hc : coverPullback J (lowerOriginalCover k) Fₖ ≫
      coverPullback J (lowerPairCover k) Fₖ =
        coverPullback J (tripleMiddleCover k) Fₖ := by
    rw [← coverPullback_comp,
      cmHarrisGeometricTripleLowerPairOriginalCoverMap_comp]
  change (_ ≫ coverPullback J (lowerOriginalCover k) Fₖ) ≫
      coverPullback J (lowerPairCover k) Fₖ =
    _ ≫ coverPullback J (tripleMiddleCover k) Fₖ
  rw [Category.assoc, hc]

/-- The previously named direct pair map has the original triple common-cover normalization. -/
@[reassoc] theorem cmHarrisGeometricTripleDirectPairCoefficientComparison_common :
    directComparison ≫ (tripleUpperIso).hom = (tripleOwnIso).hom ≫
      (association).map (cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm) := by
  rw [← cmHarrisGeometricTripleDirectPairOriginalSystemIso_factorization,
    ← Category.assoc, cmHarrisGeometricLatticeCoefficientComparison_common,
    Category.assoc, cmHarrisGeometricTripleDirectPairSystemInclusion_square,
    ← Category.assoc, cmHarrisGeometricTripleDirectPairOwnSystemIso_factorization]

/-- The previously named lower pair map has the original triple common-cover normalization. -/
@[reassoc] theorem cmHarrisGeometricTripleLowerPairCoefficientComparison_common :
    lowerComparison ≫ (tripleMiddleIso).hom = (tripleOwnIso).hom ≫
      (association).map (cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm) := by
  rw [← cmHarrisGeometricTripleLowerPairOriginalSystemIso_factorization,
    ← Category.assoc, cmHarrisGeometricLatticeCoefficientComparison_common,
    Category.assoc, cmHarrisGeometricTripleLowerPairSystemInclusion_square,
    ← Category.assoc, cmHarrisGeometricTripleLowerPairOwnSystemIso_factorization]

/-- The complete separate-cover composite is exactly the previously named direct pair map. -/
@[simp] theorem cmHarrisGeometricTripleDirectPairCoefficientComparison_eq_separate :
    directComparison = (separateChain).hom := by
  apply (cancel_mono (tripleUpperIso).hom).1
  rw [cmHarrisGeometricTripleDirectPairCoefficientComparison_common,
    cmHarrisGeometricTripleSeparateSystemChain_hom_common,
    cmHarrisGeometricTripleCommonSystemChain_hom]

/-- The first separate-cover leg is exactly the previously named lower pair map. -/
@[simp] theorem cmHarrisGeometricTripleLowerPairCoefficientComparison_eq_separate :
    lowerComparison = (separateChain).map' 0 1 := by
  apply (cancel_mono (tripleMiddleIso).hom).1
  rw [cmHarrisGeometricTripleLowerPairCoefficientComparison_common]
  change (tripleOwnIso).hom ≫
      (association).map (cmHarrisTripleLowerCoefficientInclusion D ρ p U V T hVU hTV m hm) =
    ((tripleOwnIso).hom ≫ (commonChain).map' 0 1 ≫ (tripleMiddleIso).inv) ≫
      (tripleMiddleIso).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    cmHarrisGeometricTripleCommonSystemChain_lower]

/-- Use the original lower pair morphism and the actual upper leg on separately constructed covers. -/
def cmHarrisGeometricTripleOriginalPairSystemChain :
    ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) 2 :=
  ComposableArrows.mk₂ lowerComparison ((separateChain).map' 1 2)

local notation "originalPairChain" => cmHarrisGeometricTripleOriginalPairSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- This chain with the original named lower map equals the original separate-cover triple chain. -/
@[simp] theorem cmHarrisGeometricTripleOriginalPairSystemChain_eq_separate :
    originalPairChain = separateChain := by
  change ComposableArrows.mk₂ lowerComparison ((separateChain).map' 1 2) = separateChain
  rw [cmHarrisGeometricTripleLowerPairCoefficientComparison_eq_separate]
  rfl

/-- The original-pair chain has the actual three cover changes as an isomorphism to common covers. -/
def cmHarrisGeometricTripleOriginalPairChainIso : originalPairChain ≅ commonChain :=
  eqToIso (cmHarrisGeometricTripleOriginalPairSystemChain_eq_separate D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
    ρ p m hm existence geometry hRigid) ≪≫
  cmHarrisGeometricTripleSeparateChainIso D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- Its lower leg is the original named pair comparison on the complete exponent diagram. -/
@[simp] theorem cmHarrisGeometricTripleOriginalPairSystemChain_lower :
    (originalPairChain).map' 0 1 = lowerComparison := rfl

/-- The two legs compose to the original named direct pair comparison, with no new coefficient map. -/
@[simp] theorem cmHarrisGeometricTripleOriginalPairSystemChain_hom :
    (originalPairChain).hom = directComparison := by
  change lowerComparison ≫ (separateChain).map' 1 2 = directComparison
  rw [cmHarrisGeometricTripleLowerPairCoefficientComparison_eq_separate]
  exact (cmHarrisGeometricTripleDirectPairCoefficientComparison_eq_separate D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
    ρ p m hm existence geometry hRigid).symm

/-- Every chain arrow commutes with every original exponent reduction, including exponent zero. -/
@[reassoc] theorem cmHarrisGeometricTripleOriginalPairSystemChain_transition
    {a b : Fin 3} (g : a ⟶ b) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((originalPairChain).obj a).map f ≫ ((originalPairChain).map g).app j =
      ((originalPairChain).map g).app i ≫ ((originalPairChain).obj b).map f :=
  ((originalPairChain).map g).naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
