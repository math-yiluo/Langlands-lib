import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeComparison
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoarseAssociatedSystem
import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem

/-! # Canonical lattice comparison on the separate original geometric coefficient covers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
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

variable (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor V.obj)

local notation "XV" => (geometricSchemes).obj V
local notation "J" => Scheme.smallEtaleTopology XV
local notation "R" => HarrisCoefficientIntegers K p
local notation "commonLevel" k:arg => cmHarrisLatticeCommonLevel D ρ p U V hVU m hm k
local notation "commonh" k:arg => cmHarrisLatticeCommonLevel_le D ρ p U V hVU m hm k
local notation "groups" => cmHarrisLatticeCommonGroups D ρ p U V hVU m hm
local notation "ownGroups" => cmHarrisCoefficientGroups D ρ p V m hm
local notation "coarseGroups" => cmHarrisCoarseCoefficientGroups D ρ p U V hVU m hm
local notation "ownGroupMap" => cmHarrisLatticeCommonOwnGroupMap D ρ p U V hVU m hm
local notation "coarseGroupMap" => cmHarrisLatticeCommonCoarseGroupMap D ρ p U V hVU m hm
local notation "ownCoefficients" => cmHarrisCoefficientDiagram D ρ p V m hm
local notation "coarseCoefficients" => cmHarrisCoarseCoefficientDiagram D ρ p U V hVU m hm
local notation "commonOwnCoefficients" => cmHarrisLatticeCommonOwnCoefficients D ρ p U V hVU m hm
local notation "commonCoarseCoefficients" =>
  cmHarrisLatticeCommonOriginalCoefficients D ρ p U V hVU m hm
local notation "commonCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "commonProperty" => cmHarrisGeometricLatticeCommonEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "ownCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V
    ρ p m hm existence geometry hRigid
local notation "ownProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V
    ρ p m hm existence geometry hRigid
local notation "coarseCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "coarseProperty" => cmHarrisGeometricCoarseEtaleDiagram_isFiniteGeometricTorsor D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "commonOwnSystem" => cmHarrisGeometricLatticeCommonOwnSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "commonCoarseSystem" => cmHarrisGeometricLatticeCommonOriginalSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "ownSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q V
    ρ p m hm existence geometry hRigid
local notation "coarseSystem" => cmHarrisGeometricCoarseAssociatedSystem D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid
local notation "commonCoefficientMap" => cmHarrisGeometricLatticeCommonCoefficientInclusion D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid

local notation "ownLevel" k:arg => cmHarrisCoefficientLevel D ρ p V m hm k
local notation "ownh" k:arg => cmHarrisCoefficientLevel_le D ρ p V m hm k
local notation "ownRefinement" k:arg => cmHarrisLatticeCommonLevel_le_own D ρ p U V hVU m hm k

/-- The actual common-kernel forgetting map to the existing own coefficient cover. -/
def cmHarrisGeometricLatticeCommonOwnCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (ownCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (ownh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "ownCoverMap" k:arg => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k

/-- Its underlying map is the original geometric tower inclusion. -/
@[simp] theorem cmHarrisGeometricLatticeCommonOwnCoverMap_left (k : ℕᵒᵖ) :
    (ownCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) := rfl

/-- The actual forgetting maps commute with all original exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOwnCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ ownCoverMap j =
      ownCoverMap i ≫ (ownCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (ownRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (ownRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisCoefficientLevel_antitone D ρ p V m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- Equivariance uses the original quotient map and inverse-right deck actions. -/
def cmHarrisGeometricLatticeCommonOwnActionMap (k : ℕᵒᵖ) :
    (commonCovers).action k ⟶
      (Action.res (XV).Etale ((ownGroupMap).app k).hom).obj ((ownCovers).action k) where
  hom := ownCoverMap k
  comm g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D V (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (ownRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D V (ownLevel k.unop) (ownh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "ownActionMap" k:arg => cmHarrisGeometricLatticeCommonOwnActionMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k
local notation "ownInc" k:arg =>
  etaleAssociatedInclusion XV ((ownCovers).action k) ((ownCoefficients).action k)
local notation "commonOwnInc" k:arg =>
  etaleAssociatedInclusion XV ((commonCovers).action k) ((commonOwnCoefficients).action k)

/-- Change only the cover coordinate, retaining the original own coefficient. -/
def cmHarrisGeometricLatticeCommonOwnAssociatedComparison (k : ℕᵒᵖ) :
    (ownSystem).obj k ⟶ (commonOwnSystem).obj k :=
  etaleCrossCoverMap XV ((ownGroupMap).app k).hom (ownActionMap k)
    (𝟙 ((Action.res (ModuleCat.{0} R) ((ownGroupMap).app k).hom).obj
      ((ownCoefficients).action k)))

local notation "ownComparison" k:arg => cmHarrisGeometricLatticeCommonOwnAssociatedComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k

/-- Both exact cover actions are finite geometric torsors, so cover change is invertible. -/
theorem cmHarrisGeometricLatticeCommonOwnAssociatedComparison_isIso (k : ℕᵒᵖ) :
    IsIso (ownComparison k) :=
  etaleAssociatedCoverComparison XV ((ownGroups).obj k) ((groups).obj k)
    ((ownCovers).action k) ((commonCovers).action k) (ownProperty k) (commonProperty k)
    ((ownGroupMap).app k).hom (ownActionMap k) R ((ownCoefficients).action k)

/-- The normalization keeps the coefficient and pulls the actual cover coordinate. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion (k : ℕᵒᵖ) :
    ownComparison k ≫ commonOwnInc k =
      ownInc k ≫ coverPullback J (ownCoverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj k)) :=
  etaleCrossCoverMap_identity_inclusion XV R
    (A := (ownCovers).action k) (B := (commonCovers).action k)
    ((ownGroupMap).app k).hom (ownActionMap k) ((ownCoefficients).action k)

/-- Cover change commutes with every original coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOwnAssociatedComparison_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownSystem).map f ≫ ownComparison j =
      ownComparison i ≫ (commonOwnSystem).map f := by
  have hcover :
      coverPullback J (ownCoverMap j)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) ≫
        coverPullback J ((commonCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) =
      coverPullback J ((ownCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) ≫
        coverPullback J (ownCoverMap i)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) := by
    rw [← coverPullback_comp, ← coverPullback_comp]
    exact congrArg (fun b => coverPullback J b
      ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)))
      (cmHarrisGeometricLatticeCommonOwnCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q U V
          hVU ρ p m hm existence geometry hRigid f)
  have hsource :
      (ownSystem).map f ≫ ownInc j ≫
        coverPullback J ((ownCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) =
      ownInc i ≫ (productSheaf J ((ownCovers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((ownCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV ownCovers ownProperty f ownCoefficients
  have hcommon :
      (commonOwnSystem).map f ≫ commonOwnInc j ≫
        coverPullback J ((commonCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) =
      commonOwnInc i ≫ (productSheaf J ((commonCovers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((ownCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV commonCovers commonProperty f commonOwnCoefficients
  apply etaleAssociatedTransition_hom_ext XV commonCovers commonProperty f commonOwnCoefficients
  simp only [Category.assoc]
  change (ownSystem).map f ≫ ownComparison j ≫ commonOwnInc j ≫
      coverPullback J ((commonCovers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j)) =
    ownComparison i ≫ (commonOwnSystem).map f ≫ commonOwnInc j ≫
      coverPullback J ((commonCovers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j))
  rw [cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion_assoc D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigid j, hcommon,
    cmHarrisGeometricLatticeCommonOwnAssociatedComparison_inclusion_assoc D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid i, hcover]
  have hsource' := congrArg (fun b => b ≫ coverPullback J (ownCoverMap i)
    ((constantSheaf J (ModuleCat.{0} R)).obj ((ownCoefficients).obj.obj j))) hsource
  simpa only [Category.assoc, coverPullback_natural] using hsource'

/-- The entire own system compares to its association on the common covers. -/
def cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso : ownSystem ≅ commonOwnSystem :=
  NatIso.ofComponents (fun k => by
    letI := cmHarrisGeometricLatticeCommonOwnAssociatedComparison_isIso D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid k
    exact asIso (ownComparison k))
    (fun f => cmHarrisGeometricLatticeCommonOwnAssociatedComparison_naturality D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid f)

local notation "ownCoverIso" => cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso_hom_app (k : ℕᵒᵖ) :
    (ownCoverIso).hom.app k = ownComparison k := rfl

/-- Its inverse also preserves every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonOwnSystem).map f ≫ (ownCoverIso).inv.app j =
      (ownCoverIso).inv.app i ≫ (ownSystem).map f :=
  (ownCoverIso).inv.naturality f

local notation "coarseLevel" k:arg => cmHarrisCoarseCoefficientLevel D ρ p U V hVU m hm k
local notation "coarseh" k:arg => cmHarrisCoarseCoefficientLevel_le_coarse D ρ p U V hVU m hm k
local notation "coarseRefinement" k:arg => cmHarrisLatticeCommonLevel_le_coarse D ρ p U V hVU m hm k

/-- The actual common-kernel forgetting map to the existing coarse coefficient cover. -/
def cmHarrisGeometricLatticeCommonCoarseCoverMap (k : ℕᵒᵖ) :
    (commonCovers).obj.obj k ⟶ (coarseCovers).obj.obj k :=
  MorphismProperty.Over.homMk
    ((geometricSchemes).map (smallCMInclusion D (coarseRefinement k.unop))) (by
      change (geometricSchemes).map (smallCMInclusion D (coarseRefinement k.unop)) ≫
          (geometricSchemes).map (smallCMInclusion D (coarseh k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (commonh k.unop))
      rw [← (geometricSchemes).map_comp, smallCMInclusion_trans])

local notation "coarseCoverMap" k:arg => cmHarrisGeometricLatticeCommonCoarseCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k

/-- Its underlying map is the original geometric tower inclusion. -/
@[simp] theorem cmHarrisGeometricLatticeCommonCoarseCoverMap_left (k : ℕᵒᵖ) :
    (coarseCoverMap k).left =
      (geometricSchemes).map (smallCMInclusion D (coarseRefinement k.unop)) := rfl

/-- The actual forgetting maps commute with all original exponent transitions. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoarseCoverMap_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCovers).obj.map f ≫ coarseCoverMap j =
      coarseCoverMap i ≫ (coarseCovers).obj.map f := by
  apply MorphismProperty.Over.Hom.ext
  change (geometricSchemes).map (smallCMInclusion D
      (cmHarrisLatticeCommonLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop))) ≫
        (geometricSchemes).map (smallCMInclusion D (coarseRefinement j.unop)) =
    (geometricSchemes).map (smallCMInclusion D (coarseRefinement i.unop)) ≫
      (geometricSchemes).map (smallCMInclusion D
        (cmHarrisCoarseCoefficientLevel_antitone D ρ p U V hVU m hm (leOfHom f.unop)))
  rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
    smallCMInclusion_trans, smallCMInclusion_trans]

/-- Equivariance uses the original quotient map and inverse-right deck actions. -/
def cmHarrisGeometricLatticeCommonCoarseActionMap (k : ℕᵒᵖ) :
    (commonCovers).action k ⟶
      (Action.res (XV).Etale ((coarseGroupMap).app k).hom).obj ((coarseCovers).action k) where
  hom := coarseCoverMap k
  comm g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      apply MorphismProperty.Over.Hom.ext
      change (geometricSchemes).map
          (smallCMNormalInverseArrow D V (commonLevel k.unop) (commonh k.unop) g) ≫
            (geometricSchemes).map (smallCMInclusion D (coarseRefinement k.unop)) =
        (geometricSchemes).map (smallCMInclusion D (coarseRefinement k.unop)) ≫
          (geometricSchemes).map
            (smallCMNormalInverseArrow D V (coarseLevel k.unop) (coarseh k.unop) g)
      rw [← (geometricSchemes).map_comp, ← (geometricSchemes).map_comp,
        smallCMNormalInverseArrow_inclusion]

local notation "coarseActionMap" k:arg => cmHarrisGeometricLatticeCommonCoarseActionMap D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k
local notation "coarseInc" k:arg =>
  etaleAssociatedInclusion XV ((coarseCovers).action k) ((coarseCoefficients).action k)
local notation "commonCoarseInc" k:arg =>
  etaleAssociatedInclusion XV ((commonCovers).action k) ((commonCoarseCoefficients).action k)

/-- Change only the cover coordinate, retaining the original coarse coefficient. -/
def cmHarrisGeometricLatticeCommonCoarseAssociatedComparison (k : ℕᵒᵖ) :
    (coarseSystem).obj k ⟶ (commonCoarseSystem).obj k :=
  etaleCrossCoverMap XV ((coarseGroupMap).app k).hom (coarseActionMap k)
    (𝟙 ((Action.res (ModuleCat.{0} R) ((coarseGroupMap).app k).hom).obj
      ((coarseCoefficients).action k)))

local notation "coarseComparison" k:arg => cmHarrisGeometricLatticeCommonCoarseAssociatedComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid k

/-- Both exact cover actions are finite geometric torsors, so cover change is invertible. -/
theorem cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_isIso (k : ℕᵒᵖ) :
    IsIso (coarseComparison k) :=
  etaleAssociatedCoverComparison XV ((coarseGroups).obj k) ((groups).obj k)
    ((coarseCovers).action k) ((commonCovers).action k) (coarseProperty k) (commonProperty k)
    ((coarseGroupMap).app k).hom (coarseActionMap k) R ((coarseCoefficients).action k)

/-- The normalization keeps the coefficient and pulls the actual cover coordinate. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion (k : ℕᵒᵖ) :
    coarseComparison k ≫ commonCoarseInc k =
      coarseInc k ≫ coverPullback J (coarseCoverMap k)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj k)) :=
  etaleCrossCoverMap_identity_inclusion XV R
    (A := (coarseCovers).action k) (B := (commonCovers).action k)
    ((coarseGroupMap).app k).hom (coarseActionMap k) ((coarseCoefficients).action k)

/-- Cover change commutes with every original coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_naturality
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (coarseSystem).map f ≫ coarseComparison j =
      coarseComparison i ≫ (commonCoarseSystem).map f := by
  have hcover :
      coverPullback J (coarseCoverMap j)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) ≫
        coverPullback J ((commonCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) =
      coverPullback J ((coarseCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) ≫
        coverPullback J (coarseCoverMap i)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) := by
    rw [← coverPullback_comp, ← coverPullback_comp]
    exact congrArg (fun b => coverPullback J b
      ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)))
      (cmHarrisGeometricLatticeCommonCoarseCoverMap_naturality D C preservation composition unitCoherence associativity comparison symmetry stability
          square universality dualityNaturality polarizationStability compatibility h htor q U V
          hVU ρ p m hm existence geometry hRigid f)
  have hsource :
      (coarseSystem).map f ≫ coarseInc j ≫
        coverPullback J ((coarseCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) =
      coarseInc i ≫ (productSheaf J ((coarseCovers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coarseCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV coarseCovers coarseProperty f coarseCoefficients
  have hcommon :
      (commonCoarseSystem).map f ≫ commonCoarseInc j ≫
        coverPullback J ((commonCovers).obj.map f)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) =
      commonCoarseInc i ≫ (productSheaf J ((commonCovers).obj.obj i)).map
        ((constantSheaf J (ModuleCat.{0} R)).map ((coarseCoefficients).obj.map f)) :=
    etaleAssociatedTransition_inclusion XV commonCovers commonProperty f commonCoarseCoefficients
  apply etaleAssociatedTransition_hom_ext XV commonCovers commonProperty f commonCoarseCoefficients
  simp only [Category.assoc]
  change (coarseSystem).map f ≫ coarseComparison j ≫ commonCoarseInc j ≫
      coverPullback J ((commonCovers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j)) =
    coarseComparison i ≫ (commonCoarseSystem).map f ≫ commonCoarseInc j ≫
      coverPullback J ((commonCovers).obj.map f)
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j))
  rw [cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion_assoc D C preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor q U V
      hVU ρ p m hm existence geometry hRigid j, hcommon,
    cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion_assoc D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid i, hcover]
  have hsource' := congrArg (fun b => b ≫ coverPullback J (coarseCoverMap i)
    ((constantSheaf J (ModuleCat.{0} R)).obj ((coarseCoefficients).obj.obj j))) hsource
  simpa only [Category.assoc, coverPullback_natural] using hsource'

/-- The entire coarse system compares to its association on the common covers. -/
def cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso : coarseSystem ≅ commonCoarseSystem :=
  NatIso.ofComponents (fun k => by
    letI := cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_isIso D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid k
    exact asIso (coarseComparison k))
    (fun f => cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_naturality D C preservation composition unitCoherence associativity comparison symmetry stability
        square universality dualityNaturality polarizationStability compatibility h htor q U V
        hVU ρ p m hm existence geometry hRigid f)

local notation "coarseCoverIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid

@[simp] theorem cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso_hom_app (k : ℕᵒᵖ) :
    (coarseCoverIso).hom.app k = coarseComparison k := rfl

/-- Its inverse also preserves every original exponent transition. -/
@[reassoc] theorem cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (commonCoarseSystem).map f ≫ (coarseCoverIso).inv.app j =
      (coarseCoverIso).inv.app i ≫ (coarseSystem).map f :=
  (coarseCoverIso).inv.naturality f

/-- The actual canonical-lattice inclusion on the separate original coefficient covers. -/
def cmHarrisGeometricLatticeCoefficientComparison : ownSystem ⟶ coarseSystem :=
  (ownCoverIso).hom ≫ commonCoefficientMap ≫ (coarseCoverIso).inv

local notation "latticeComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability compatibility h htor q U V
    hVU ρ p m hm existence geometry hRigid

/-- The component uses the two proved changes of covers and the original coefficient inclusion. -/
@[simp] theorem cmHarrisGeometricLatticeCoefficientComparison_app (k : ℕᵒᵖ) :
    (latticeComparison).app k =
      (ownCoverIso).hom.app k ≫ (commonCoefficientMap).app k ≫
        (coarseCoverIso).inv.app k := rfl

/-- All original exponent maps commute with the geometric lattice comparison. -/
@[reassoc] theorem cmHarrisGeometricLatticeCoefficientComparison_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (ownSystem).map f ≫ (latticeComparison).app j =
      (latticeComparison).app i ≫ (coarseSystem).map f :=
  (latticeComparison).naturality f

/-- Returning to the common covers recovers precisely the original descended inclusion. -/
@[reassoc] theorem cmHarrisGeometricLatticeCoefficientComparison_common :
    latticeComparison ≫ (coarseCoverIso).hom = (ownCoverIso).hom ≫ commonCoefficientMap := by
  change ((ownCoverIso).hom ≫ commonCoefficientMap ≫ (coarseCoverIso).inv) ≫
    (coarseCoverIso).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
