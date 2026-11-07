import Langlands.Shimura.PEL.HarrisTaylorCMGeometricTripleCommon
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.Coefficients.VaryingSystemGroupCoverChange

/-! # The original three coefficient systems on their separate geometric CM covers -/

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

local notation "ownGroups" => cmHarrisCoefficientGroups D ρ p T m hm
local notation "ownGroupMap" => cmHarrisTripleOwnGroupMap D ρ p U V T hVU hTV m hm
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p T m hm
local notation "ownCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q T
    ρ p m hm existence geometry hRigid
local notation "ownProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q T
    ρ p m hm existence geometry hRigid
local notation "ownSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q T
    ρ p m hm existence geometry hRigid
local notation "ownLevel" k:arg => cmHarrisCoefficientLevel D ρ p T m hm k
local notation "ownh" k:arg => cmHarrisCoefficientLevel_le D ρ p T m hm k
local notation "ownRefinement" k:arg => cmHarrisTripleCommonLevel_le_own D ρ p U V T hVU hTV m hm k

/-- The actual simultaneous-kernel forgetting map to this original coefficient cover. -/
def cmHarrisGeometricTripleOwnCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (ownCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (ownh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "ownCoverMap" k:arg => cmHarrisGeometricTripleOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k

@[simp] theorem cmHarrisGeometricTripleOwnCoverMap_left (k : ℕᵒᵖ) :
    (ownCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) := rfl

/-- The original forgetting maps preserve all exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleOwnCoverMap_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ ownCoverMap j =
      ownCoverMap i ≫ (ownCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (ownRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (ownRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisCoefficientLevel_antitone D ρ p T m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The whole original cover map is equivariant along its actual residual quotient map. -/
def cmHarrisGeometricTripleOwnCoverDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale ownGroupMap).obj ownCovers where
  hom :=
    { app k := ownCoverMap k
      naturality _ _ f := by
        exact cmHarrisGeometricTripleOwnCoverMap_naturality D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
          ρ p m hm existence geometry hRigid f }
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (ownLevel k.unop) (ownh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "ownDiagramMap" => cmHarrisGeometricTripleOwnCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- The full independently constructed original system compares with its exact common-cover vertex. -/
def cmHarrisGeometricTripleOwnCoverIso : ownSystem ≅ (commonChain).obj' 0 :=
  (etaleAssociatedVaryingGroupCoverIso XT R ownGroupMap commonCovers ownCovers
    ownDiagramMap commonProperty ownProperty).app ownCoefficients

local notation "ownIso" => cmHarrisGeometricTripleOwnCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- Its forward map retains the original coefficient and actual common-to-original cover map. -/
@[simp] theorem cmHarrisGeometricTripleOwnCoverIso_hom_app (k : ℕᵒᵖ) :
    (ownIso).hom.app k = etaleCrossCoverMap XT ((ownGroupMap).app k).hom
      ((EquivariantDiagram.evaluation k).map ownDiagramMap)
      (𝟙 ((Action.res (ModuleCat.{0} R) ((ownGroupMap).app k).hom).obj
        ((ownCoefficients).action k))) := rfl

/-- The section formula changes only the cover coordinate. -/
@[reassoc] theorem cmHarrisGeometricTripleOwnCoverIso_inclusion (k : ℕᵒᵖ) :
    (ownIso).hom.app k ≫ commonInc 0 k =
      etaleAssociatedInclusion XT ((ownCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J (ownCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) :=
  etaleAssociatedAtGroupCoverChange_inclusion XT R ownGroupMap commonCovers ownCovers
    ownDiagramMap k ownCoefficients

/-- Its actual inverse preserves every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricTripleOwnCoverIso_inv_transition {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 0).map f ≫ (ownIso).inv.app j =
      (ownIso).inv.app i ≫ (ownSystem).map f :=
  (ownIso).inv.naturality f

local notation "middleGroups" => cmHarrisCoarseCoefficientGroups D ρ p V T hTV m hm
local notation "middleGroupMap" => cmHarrisTripleMiddleGroupMap D ρ p U V T hVU hTV m hm
local notation "middleCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p V T hTV m hm
local notation "middleCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV
    ρ p m hm existence geometry hRigid
local notation "middleProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV
    ρ p m hm existence geometry hRigid
local notation "middleSystem" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V T hTV
    ρ p m hm existence geometry hRigid
local notation "middleLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p V T hTV m hm k
local notation "middleh" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p V T hTV m hm k
local notation "middleRefinement" k:arg => cmHarrisTripleCommonLevel_le_middle D ρ p U V T hVU hTV m hm k

/-- The actual simultaneous-kernel forgetting map to this original coefficient cover. -/
def cmHarrisGeometricTripleMiddleCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (middleCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (middleRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (middleRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (middleh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "middleCoverMap" k:arg => cmHarrisGeometricTripleMiddleCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k

@[simp] theorem cmHarrisGeometricTripleMiddleCoverMap_left (k : ℕᵒᵖ) :
    (middleCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (middleRefinement k.unop)) := rfl

/-- The original forgetting maps preserve all exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleMiddleCoverMap_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ middleCoverMap j =
      middleCoverMap i ≫ (middleCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (middleRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (middleRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisCoarseCoefficientLevel_antitone D ρ p V T hTV m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The whole original cover map is equivariant along its actual residual quotient map. -/
def cmHarrisGeometricTripleMiddleCoverDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale middleGroupMap).obj middleCovers where
  hom :=
    { app k := middleCoverMap k
      naturality _ _ f := by
        exact cmHarrisGeometricTripleMiddleCoverMap_naturality D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
          ρ p m hm existence geometry hRigid f }
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (middleRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (middleRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (middleLevel k.unop) (middleh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "middleDiagramMap" => cmHarrisGeometricTripleMiddleCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- The full independently constructed original system compares with its exact common-cover vertex. -/
def cmHarrisGeometricTripleMiddleCoverIso : middleSystem ≅ (commonChain).obj' 1 :=
  (etaleAssociatedVaryingGroupCoverIso XT R middleGroupMap commonCovers middleCovers
    middleDiagramMap commonProperty middleProperty).app middleCoefficients

local notation "middleIso" => cmHarrisGeometricTripleMiddleCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- Its forward map retains the original coefficient and actual common-to-original cover map. -/
@[simp] theorem cmHarrisGeometricTripleMiddleCoverIso_hom_app (k : ℕᵒᵖ) :
    (middleIso).hom.app k = etaleCrossCoverMap XT ((middleGroupMap).app k).hom
      ((EquivariantDiagram.evaluation k).map middleDiagramMap)
      (𝟙 ((Action.res (ModuleCat.{0} R) ((middleGroupMap).app k).hom).obj
        ((middleCoefficients).action k))) := rfl

/-- The section formula changes only the cover coordinate. -/
@[reassoc] theorem cmHarrisGeometricTripleMiddleCoverIso_inclusion (k : ℕᵒᵖ) :
    (middleIso).hom.app k ≫ commonInc 1 k =
      etaleAssociatedInclusion XT ((middleCovers).action k) ((middleCoefficients).action k) ≫
        coverPullback J (middleCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((middleCoefficients).obj.obj k)) :=
  etaleAssociatedAtGroupCoverChange_inclusion XT R middleGroupMap commonCovers middleCovers
    middleDiagramMap k middleCoefficients

/-- Its actual inverse preserves every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricTripleMiddleCoverIso_inv_transition {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 1).map f ≫ (middleIso).inv.app j =
      (middleIso).inv.app i ≫ (middleSystem).map f :=
  (middleIso).inv.naturality f

local notation "upperGroups" => cmHarrisCoarseCoefficientGroups D ρ p U T hTU m hm
local notation "upperGroupMap" => cmHarrisTripleUpperGroupMap D ρ p U V T hVU hTV m hm
local notation "upperCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U T hTU m hm
local notation "upperCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU
    ρ p m hm existence geometry hRigid
local notation "upperProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU
    ρ p m hm existence geometry hRigid
local notation "upperSystem" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U T hTU
    ρ p m hm existence geometry hRigid
local notation "upperLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U T hTU m hm k
local notation "upperh" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U T hTU m hm k
local notation "upperRefinement" k:arg => cmHarrisTripleCommonLevel_le_upper D ρ p U V T hVU hTV m hm k

/-- The actual simultaneous-kernel forgetting map to this original coefficient cover. -/
def cmHarrisGeometricTripleUpperCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (upperCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (upperRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (upperRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (upperh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "upperCoverMap" k:arg => cmHarrisGeometricTripleUpperCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid k

@[simp] theorem cmHarrisGeometricTripleUpperCoverMap_left (k : ℕᵒᵖ) :
    (upperCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (upperRefinement k.unop)) := rfl

/-- The original forgetting maps preserve all exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperCoverMap_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ upperCoverMap j =
      upperCoverMap i ≫ (upperCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisTripleCommonLevel_antitone D ρ p U V T hVU hTV m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (upperRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (upperRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisCoarseCoefficientLevel_antitone D ρ p U T hTU m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- The whole original cover map is equivariant along its actual residual quotient map. -/
def cmHarrisGeometricTripleUpperCoverDiagramMap :
    commonCovers ⟶
      (EquivariantDiagram.groupRestriction (XT).Etale upperGroupMap).obj upperCovers where
  hom :=
    { app k := upperCoverMap k
      naturality _ _ f := by
        exact cmHarrisGeometricTripleUpperCoverMap_naturality D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
          ρ p m hm existence geometry hRigid f }
  comm k g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D T (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (upperRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (upperRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D T (upperLevel k.unop) (upperh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "upperDiagramMap" => cmHarrisGeometricTripleUpperCoverDiagramMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- The full independently constructed original system compares with its exact common-cover vertex. -/
def cmHarrisGeometricTripleUpperCoverIso : upperSystem ≅ (commonChain).obj' 2 :=
  (etaleAssociatedVaryingGroupCoverIso XT R upperGroupMap commonCovers upperCovers
    upperDiagramMap commonProperty upperProperty).app upperCoefficients

local notation "upperIso" => cmHarrisGeometricTripleUpperCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- Its forward map retains the original coefficient and actual common-to-original cover map. -/
@[simp] theorem cmHarrisGeometricTripleUpperCoverIso_hom_app (k : ℕᵒᵖ) :
    (upperIso).hom.app k = etaleCrossCoverMap XT ((upperGroupMap).app k).hom
      ((EquivariantDiagram.evaluation k).map upperDiagramMap)
      (𝟙 ((Action.res (ModuleCat.{0} R) ((upperGroupMap).app k).hom).obj
        ((upperCoefficients).action k))) := rfl

/-- The section formula changes only the cover coordinate. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperCoverIso_inclusion (k : ℕᵒᵖ) :
    (upperIso).hom.app k ≫ commonInc 2 k =
      etaleAssociatedInclusion XT ((upperCovers).action k) ((upperCoefficients).action k) ≫
        coverPullback J (upperCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((upperCoefficients).obj.obj k)) :=
  etaleAssociatedAtGroupCoverChange_inclusion XT R upperGroupMap commonCovers upperCovers
    upperDiagramMap k upperCoefficients

/-- Its actual inverse preserves every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricTripleUpperCoverIso_inv_transition {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((commonChain).obj' 2).map f ≫ (upperIso).inv.app j =
      (upperIso).inv.app i ≫ (upperSystem).map f :=
  (upperIso).inv.naturality f

/-- The original three separately associated systems and actual common-cover coefficient comparisons. -/
def cmHarrisGeometricTripleSeparateSystemChain :
    ComposableArrows (ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{0} R)) 2 :=
  ComposableArrows.mk₂
    ((ownIso).hom ≫ (commonChain).map' 0 1 ≫ (middleIso).inv)
    ((middleIso).hom ≫ (commonChain).map' 1 2 ≫ (upperIso).inv)

local notation "separateChain" => cmHarrisGeometricTripleSeparateSystemChain D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

/-- All three actual cover changes give one isomorphism of the complete coefficient-system chains. -/
def cmHarrisGeometricTripleSeparateChainIso : separateChain ≅ commonChain :=
  ComposableArrows.isoMk₂ ownIso middleIso upperIso
    (by
      change ((ownIso).hom ≫ (commonChain).map' 0 1 ≫ (middleIso).inv) ≫ (middleIso).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change ((middleIso).hom ≫ (commonChain).map' 1 2 ≫ (upperIso).inv) ≫ (upperIso).hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

local notation "chainIso" => cmHarrisGeometricTripleSeparateChainIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricTripleSeparateSystemChain_own :
    (separateChain).obj' 0 = ownSystem := rfl

@[simp] theorem cmHarrisGeometricTripleSeparateSystemChain_middle :
    (separateChain).obj' 1 = middleSystem := rfl

@[simp] theorem cmHarrisGeometricTripleSeparateSystemChain_upper :
    (separateChain).obj' 2 = upperSystem := rfl

/-- Returning the complete composite to the common covers recovers the original direct inclusion. -/
@[reassoc] theorem cmHarrisGeometricTripleSeparateSystemChain_hom_common :
    (separateChain).hom ≫ (upperIso).hom = (ownIso).hom ≫ (commonChain).hom :=
  (chainIso).hom.naturality (homOfLE (show (0 : Fin 3) ≤ 2 by decide))

/-- The two actual separate-cover legs compose to the common-cover direct map transported back. -/
@[simp] theorem cmHarrisGeometricTripleSeparateSystemChain_hom :
    (separateChain).hom = (ownIso).hom ≫ (commonChain).hom ≫ (upperIso).inv := by
  apply (cancel_mono (upperIso).hom).1
  rw [cmHarrisGeometricTripleSeparateSystemChain_hom_common]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The complete composite is the original direct coefficient inclusion descended on actual covers. -/
@[simp] theorem cmHarrisGeometricTripleSeparateSystemChain_hom_original :
    (separateChain).hom = (ownIso).hom ≫
      (association).map (cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm) ≫
        (upperIso).inv := by
  rw [cmHarrisGeometricTripleSeparateSystemChain_hom,
    cmHarrisGeometricTripleCommonSystemChain_hom]

/-- On actual invariant sections the complete separate-cover composite applies the original direct coefficient map. -/
@[reassoc] theorem cmHarrisGeometricTripleSeparateSystemChain_hom_inclusion (k : ℕᵒᵖ) :
    (separateChain).hom.app k ≫ (upperIso).hom.app k ≫ commonInc 2 k =
      etaleAssociatedInclusion XT ((ownCovers).action k) ((ownCoefficients).action k) ≫
        coverPullback J (ownCoverMap k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) ≫
        (productSheaf J ((commonCovers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map
            ((cmHarrisTripleDirectCoefficientInclusion D ρ p U V T hVU hTV m hm).hom.app k)) := by
  have e := congrArg (fun b => b.app k)
    (cmHarrisGeometricTripleSeparateSystemChain_hom_common D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U V T hVU hTV
      ρ p m hm existence geometry hRigid)
  change (separateChain).hom.app k ≫ (upperIso).hom.app k =
    (ownIso).hom.app k ≫ (commonChain).hom.app k at e
  rw [← Category.assoc, e, Category.assoc,
    cmHarrisGeometricTripleCommonSystemChain_hom_inclusion, ← Category.assoc,
    cmHarrisGeometricTripleOwnCoverIso_inclusion]
  simp only [Category.assoc]

/-- Every arrow of the separate-cover chain retains all original exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricTripleSeparateSystemChain_transition
    {a b : Fin 3} (g : a ⟶ b) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((separateChain).obj a).map f ≫ ((separateChain).map g).app j =
      ((separateChain).map g).app i ≫ ((separateChain).obj b).map f :=
  ((separateChain).map g).naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
