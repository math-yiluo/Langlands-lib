import Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeInverseImage
import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientLevelSystem
import Langlands.Shimura.Coefficients.EtaleInverseImageProductIdentity

/-! # Identity of the original geometric Harris lattice inverse-image comparison -/

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
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

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

variable (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)
  (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "XU" => (geometricSchemes).obj U
local notation "J" => Scheme.smallEtaleTopology XU
local notation "R" => HarrisCoefficientIntegers K p
local notation "baseMap" => (geometricSchemes).map (smallCMInclusion D (le_refl U.obj.subgroup))
local notation "originalSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "originalCovers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
local notation "originalCoefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "coarseCovers" => cmHarrisGeometricCoarseEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "commonCovers" => cmHarrisGeometricLatticeCommonEtaleDiagram D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "commonOwnMap" => cmHarrisGeometricLatticeCommonOwnCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "commonCoarseMap" => cmHarrisGeometricLatticeCommonCoarseCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "coarseCoverMap" => cmHarrisGeometricCoarsePullbackCoverMap D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid
local notation "inverseIso" => cmHarrisGeometricCoarseInverseImageAssociatedIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid
local notation "latticeComparison" => cmHarrisGeometricLatticeCoefficientComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "originalDelta" => cmHarrisGeometricLatticeInverseImageComparison D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid
local notation "coarseCoverIso" => cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid
local notation "originalInc" k:arg => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k
local notation "coarseInc" k:arg => cmHarrisGeometricCoarseAssociatedInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid k
local notation "commonInc" k:arg => cmHarrisGeometricLatticeCommonOriginalInclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid k

omit [Module.Finite ℚ A] in
/-- The actual represented tower map of a reflexive inclusion is the scheme identity. -/
theorem cmHarrisGeometricLatticeBaseMap_id : baseMap = 𝟙 XU := by
  rw [smallCMInclusion_refl, (geometricSchemes).map_id]

local notation "baseEq" => cmHarrisGeometricLatticeBaseMap_id D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U
local notation "congrCover" k:arg => (etaleObjectPullbackCongr baseEq).app ((originalCovers).obj.obj k)
local notation "idCover" k:arg => (etaleObjectPullbackId XU).app ((originalCovers).obj.obj k)
local notation "modAt" k:arg => (originalCoefficients).obj.obj k
local notation "constantU" k:arg => (constantSheaf J (ModuleCat.{0} R)).obj (modAt k)
local notation "originalProduct" k:arg => (productSheaf J ((originalCovers).obj.obj k)).obj (constantU k)

/-- Both literal common-cover routes coincide after actual base identity transport. -/
theorem cmHarrisGeometricLatticeCover_id (k : ℕᵒᵖ) :
    commonCoarseMap k ≫ coarseCoverMap k ≫ (congrCover k).hom ≫ (idCover k).hom =
      commonOwnMap k := by
  apply MorphismProperty.Over.Hom.ext
  change (commonCoarseMap k).left ≫ (coarseCoverMap k).left ≫
      ((congrCover k).hom).left ≫ pullback.fst ((originalCovers).obj.obj k).hom (𝟙 XU) =
    (commonOwnMap k).left
  have hfst : ((congrCover k).hom).left ≫
      pullback.fst ((originalCovers).obj.obj k).hom (𝟙 XU) =
      pullback.fst ((originalCovers).obj.obj k).hom baseMap :=
    etaleObjectPullbackCongr_hom_fst baseEq ((originalCovers).obj.obj k)
  rw [hfst,
    cmHarrisGeometricCoarsePullbackCoverMap_fst D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid k]
  change (geometricSchemes).map (smallCMInclusion D _) ≫
      (geometricSchemes).map (smallCMInclusion D _) =
    (geometricSchemes).map (smallCMInclusion D _)
  rw [← (geometricSchemes).map_comp, smallCMInclusion_trans]

/-- The same cover identity retains the inverse identity-pullback comparison. -/
theorem cmHarrisGeometricLatticeCover_id_inv (k : ℕᵒᵖ) :
    commonCoarseMap k ≫ coarseCoverMap k ≫ (congrCover k).hom =
      commonOwnMap k ≫ (idCover k).inv := by
  apply (cancel_mono (idCover k).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact cmHarrisGeometricLatticeCover_id D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k

/-- The original constant-product cover coordinates normalize to the inverse-image identity. -/
@[reassoc] theorem cmHarrisGeometricLatticeConstantProduct_id (k : ℕᵒᵖ) :
    inverseImageConstantProductMap baseMap R ((originalCovers).obj.obj k) (modAt k) ≫
        coverPullback J (coarseCoverMap k) (constantU k) ≫
        coverPullback J (commonCoarseMap k) (constantU k) =
      (inverseImageCongr R baseEq).hom.app (originalProduct k) ≫
        (inverseImageId R XU).hom.app (originalProduct k) ≫
        coverPullback J (commonOwnMap k) (constantU k) := by
  have hc := cmHarrisGeometricLatticeCover_id_inv D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k
  simp only [Iso.app_hom, Iso.app_inv] at hc
  rw [← inverseImageConstantProductMap_congr baseMap R baseEq]
  simp only [Category.assoc]
  rw [← coverPullback_comp, ← coverPullback_comp]
  simp only [Category.assoc]
  rw [hc, coverPullback_comp, inverseImageConstantProductMap_id_assoc]

/-- The canonical normalization uses the actual tower equality and inverse-image identity. -/
def cmHarrisGeometricLatticeIdentityNormalization :
    originalSystem ⋙ inverseImage baseMap R ≅ originalSystem :=
  Functor.isoWhiskerLeft originalSystem
      (inverseImageCongr R baseEq ≪≫ inverseImageId R XU) ≪≫
    Functor.rightUnitor originalSystem

local notation "normalization" => cmHarrisGeometricLatticeIdentityNormalization D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid

/-- Each component retains both canonical base-identity comparisons. -/
@[simp] theorem cmHarrisGeometricLatticeIdentityNormalization_hom_app (k : ℕᵒᵖ) :
    (normalization).hom.app k =
      (inverseImageCongr R baseEq).hom.app ((originalSystem).obj k) ≫
        (inverseImageId R XU).hom.app ((originalSystem).obj k) := by
  change (_ ≫ _) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The normalized comparison commutes with every original coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricLatticeIdentityNormalization_transition
    {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (inverseImage baseMap R).map ((originalSystem).map a) ≫ (normalization).hom.app j =
      (normalization).hom.app i ≫ (originalSystem).map a :=
  (normalization).hom.naturality a

/-- At a reflexive level inclusion the original reduced coefficient map is identity. -/
@[simp] theorem cmHarrisLatticeCommonCoefficientInclusion_refl (k : ℕᵒᵖ) :
    ((cmHarrisLatticeCommonCoefficientInclusion D ρ p U U le_rfl m hm).hom.app k) =
      𝟙 (modAt k) := by
  change ((cmHarrisTorsionSystemInclusion D ρ p U U le_rfl m).app k).hom = _
  exact cmHarrisTorsionSystemInclusion_refl D ρ p m k U

/-- The original lattice comparison keeps exactly the common-cover coordinate at identity. -/
@[reassoc] theorem cmHarrisGeometricLatticeCoefficientComparison_id_inclusion (k : ℕᵒᵖ) :
    (latticeComparison).app k ≫ (coarseCoverIso).hom.app k ≫ commonInc k =
      originalInc k ≫ coverPullback J (commonOwnMap k) (constantU k) := by
  have hc := cmHarrisGeometricLatticeInverseImageComparison_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid k
  simp only [cmHarrisGeometricLatticeInverseImageComparison_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] at hc
  rw [cmHarrisLatticeCommonCoefficientInclusion_refl] at hc
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  exact hc

/-- The original coarse inverse-image comparison has the same normalized common-cover sections. -/
@[reassoc] theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_id_inclusion (k : ℕᵒᵖ) :
    (inverseIso).hom.app k ≫ (coarseCoverIso).hom.app k ≫ commonInc k =
      (normalization).hom.app k ≫ originalInc k ≫
        coverPullback J (commonOwnMap k) (constantU k) := by
  have hcov : (coarseCoverIso).hom.app k ≫ commonInc k =
      coarseInc k ≫ coverPullback J (commonCoarseMap k) (constantU k) :=
    cmHarrisGeometricLatticeCommonCoarseAssociatedComparison_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid k
  rw [hcov,
    cmHarrisGeometricCoarseInverseImageAssociatedIso_hom_inclusion_assoc D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U U le_rfl ρ p m hm existence geometry hRigid hRigid k]
  change (inverseImage baseMap R).map (originalInc k) ≫
      inverseImageConstantProductMap baseMap R ((originalCovers).obj.obj k) (modAt k) ≫
      coverPullback J (coarseCoverMap k) (constantU k) ≫
      coverPullback J (commonCoarseMap k) (constantU k) = _
  rw [cmHarrisGeometricLatticeConstantProduct_id D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k,
    NatTrans.naturality_assoc, NatTrans.naturality_assoc,
    cmHarrisGeometricLatticeIdentityNormalization_hom_app]
  simp only [Category.assoc, CategoryTheory.Functor.id_map]

/-- The original coarse comparison equals canonical normalization followed by the original lattice map. -/
theorem cmHarrisGeometricCoarseInverseImageAssociatedIso_id :
    (inverseIso).hom = (normalization).hom ≫ latticeComparison := by
  apply NatTrans.ext
  funext k
  apply (cancel_mono ((coarseCoverIso).hom.app k)).1
  apply (cancel_mono (commonInc k)).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [cmHarrisGeometricCoarseInverseImageAssociatedIso_id_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k,
    cmHarrisGeometricLatticeCoefficientComparison_id_inclusion D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k]

/-- The original self-level lattice morphism is the inverse of the canonical normalization. -/
theorem cmHarrisGeometricLatticeInverseImageComparison_id_inv :
    originalDelta = (normalization).inv := by
  apply (cancel_epi (normalization).hom).1
  change (normalization).hom ≫ (latticeComparison ≫ (inverseIso).inv) = _
  rw [← Category.assoc,
    ← cmHarrisGeometricCoarseInverseImageAssociatedIso_id D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    Iso.hom_inv_id, Iso.hom_inv_id]

/-- The actual original lattice inverse-image morphism satisfies the full system identity law. -/
theorem cmHarrisGeometricLatticeInverseImageComparison_id :
    originalDelta ≫ (normalization).hom = 𝟙 originalSystem := by
  rw [cmHarrisGeometricLatticeInverseImageComparison_id_inv D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid,
    Iso.inv_hom_id]

/-- At every exponent the original morphism uses actual equality transport and inverse-image identity. -/
@[reassoc] theorem cmHarrisGeometricLatticeInverseImageComparison_id_app (k : ℕᵒᵖ) :
    (originalDelta).app k ≫
        (inverseImageCongr R baseEq).hom.app ((originalSystem).obj k) ≫
        (inverseImageId R XU).hom.app ((originalSystem).obj k) =
      𝟙 ((originalSystem).obj k) := by
  have hc := congrArg (fun a => a.app k) (cmHarrisGeometricLatticeInverseImageComparison_id D C preservation composition unitCoherence associativity comparison symmetry stability square universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid)
  simpa only [NatTrans.comp_app, NatTrans.id_app,
    cmHarrisGeometricLatticeIdentityNormalization_hom_app] using hc

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
