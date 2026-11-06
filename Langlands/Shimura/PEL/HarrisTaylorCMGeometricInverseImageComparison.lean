import Langlands.Shimura.PEL.HarrisTaylorCMGeometricAssociatedSystem
import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem

/-! # Inverse-image comparison for exact geometric CM coefficient systems -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
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
open Langlands.Shimura.Coefficients Langlands.Geometry
open Langlands.Geometry.EtaleInverseImage

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

local notation "geometricSchemes" => cmGeometricSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor
variable (q : CMRepresentabilityStatement D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability compatibility h htor)
  (U : SmallCMLevel D)
  [Module.Finite ℚ A]
  {K : Type} [Field K] [NumberField K]
  {W : Type} [AddCommGroup W] [Module K W] [Module.Finite K W]
  (ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W)
  (p : Global.FinitePlace ℚ) (m : ℕ) (hm : m ≠ 0)

variable (existence : RelativeDualSchemeExistenceStatement.{0})
  (geometry : RelativeDualSchemeGeometryStatement.{0})
  (hRigid : CMGeometricCoarseRigidity D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    compatibility h htor U.obj)

local notation "Xbar" => Functor.obj (geometricSchemes q) U
local notation "Jbar" => Scheme.smallEtaleTopology Xbar
local notation "R" => HarrisCoefficientIntegers K p
local notation "groups" => cmHarrisCoefficientGroups D ρ p U m hm
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisGeometricCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisGeometricCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "torsor" k => cmHarrisGeometricCoefficientTorsor D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k

local notation "fieldProjection" => cmGeometricProjection D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "π" => (fieldProjection).app U
local notation "schemes" => cmSchemeTower D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q
local notation "X" => (schemes).obj U
local notation "J" => Scheme.smallEtaleTopology X
local notation "originalCovers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "pulledCovers" => (etaleTorsorDiagramPullback π groups).obj originalCovers
local notation "coverIso" => cmHarrisGeometricCoefficientEtaleDiagramPullbackIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "coverSystemIso" => cmHarrisGeometricAssociatedCoefficientSystemCoverIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "originalSystem" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "pulledSystem" => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "associatedSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "originalInc" => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "inc" => cmHarrisGeometricAssociatedCoefficientSystemInclusion D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Inverse image of the original full Harris coefficient system is the system
associated to the exact geometric CM coefficient covers, with all reductions. -/
def cmHarrisGeometricCoefficientSystemAssociatedIso :
    pulledSystem ≅ associatedSystem :=
  (etaleAssociatedVaryingSystemInverseImage π R originalCovers originalProperty).app
      coefficients ≪≫ coverSystemIso

local notation "systemIso" => cmHarrisGeometricCoefficientSystemAssociatedIso D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The component uses the arbitrary-morphism comparison followed by pullback
along the canonical cartesian cover map, retaining the coefficient action. -/
@[simp] theorem cmHarrisGeometricCoefficientSystemAssociatedIso_hom_app (k : ℕᵒᵖ) :
    (systemIso).hom.app k =
      (inverseImageConstantAssociatedIso π R ((originalCovers).action k)
        (originalProperty k)).hom.app ((coefficients).action k) ≫
      etaleCrossCoverMap Xbar (MonoidHom.id ((groups).obj k))
        ((EquivariantDiagram.evaluation k).map (coverIso).hom)
        (𝟙 ((coefficients).action k)) := rfl

/-- The inverse component reverses both specified comparisons. -/
@[simp] theorem cmHarrisGeometricCoefficientSystemAssociatedIso_inv_app (k : ℕᵒᵖ) :
    (systemIso).inv.app k =
      etaleCrossCoverMap Xbar (MonoidHom.id ((groups).obj k))
        ((EquivariantDiagram.evaluation k).map (coverIso).inv)
        (𝟙 ((coefficients).action k)) ≫
      (inverseImageConstantAssociatedIso π R ((originalCovers).action k)
        (originalProperty k)).inv.app ((coefficients).action k) := rfl

/-- The comparison intertwines the inverse images of the original reductions
with the actual inverse-cover transitions on the exact geometric covers. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSystemAssociatedIso_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (inverseImage π R).map ((originalSystem).map f) ≫ (systemIso).hom.app j =
      (systemIso).hom.app i ≫ (associatedSystem).map f :=
  (systemIso).hom.naturality f

/-- The inverse comparison also respects every specified reduction. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSystemAssociatedIso_inv_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (associatedSystem).map f ≫ (systemIso).inv.app j =
      (systemIso).inv.app i ≫ (inverseImage π R).map ((originalSystem).map f) :=
  (systemIso).inv.naturality f

/-- On invariant inclusions, the comparison is inverse image of the original
inclusion, product-sheaf base change, constant-coefficient comparison and the
original cartesian cover-coordinate pullback. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSystemAssociatedIso_hom_inclusion
    (k : ℕᵒᵖ) :
    (systemIso).hom.app k ≫ (inc) k =
      (inverseImage π R).map ((originalInc) k) ≫
        (inverseImageProductSheafIso π R ((originalCovers).action k)
          (originalProperty k)
          ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj k))).hom ≫
        (productSheaf Jbar ((pulledCovers).obj.obj k)).map
          ((inverseImageConstantIso π R).hom.app ((coefficients).obj.obj k)) ≫
        coverPullback Jbar ((coverIso).hom.hom.app k)
          ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) := by
  change ((inverseImageConstantAssociatedIso π R ((originalCovers).action k)
    (originalProperty k)).hom.app ((coefficients).action k) ≫
      (coverSystemIso).hom.app k) ≫ (inc) k = _
  rw [Category.assoc, cmHarrisGeometricAssociatedCoefficientSystemCoverIso_hom_inclusion]
  exact inverseImageConstantAssociatedIso_hom_inclusion_assoc π R
    ((originalCovers).action k) (originalProperty k) ((coefficients).action k) _

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
