import Langlands.Shimura.PEL.HarrisTaylorCMGeometricInverseImageComparison

/-! # Exact-cover trivialization of inverse-image CM coefficient systems -/

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
open Langlands.Shimura.Coefficients

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

local notation "pulledSystem" => cmHarrisGeometricCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "associatedSystem" => cmHarrisGeometricAssociatedCoefficientSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "systemIso" => cmHarrisGeometricCoefficientSystemAssociatedIso D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "localizeOn" Z => (Jbar).overPullback (ModuleCat.{0} R) Z

/-- Invariant evaluation of the existing inverse-image coefficient sheaf along
an actual lift to its exact geometric coefficient cover. -/
def cmHarrisGeometricCoefficientEvaluationAlong (k : ℕᵒᵖ)
    {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj k) :
    (localizeOn Z).obj ((pulledSystem).obj k) ⟶
      (localizeOn Z).obj
        ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  (localizeOn Z).map ((systemIso).hom.app k) ≫
    etaleAssociatedEvaluationAlong Xbar covers coefficients k a

local notation "evaluationAlong" => cmHarrisGeometricCoefficientEvaluationAlong D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The specified invariant evaluation is invertible on any such lifted etale
object, and in particular on the exact coefficient cover itself. -/
def cmHarrisGeometricCoefficientTrivializationAlong (k : ℕᵒᵖ)
    {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj k) :
    (localizeOn Z).obj ((pulledSystem).obj k) ≅
      (localizeOn Z).obj
        ((constantSheaf Jbar (ModuleCat.{0} R)).obj ((coefficients).obj.obj k)) :=
  (localizeOn Z).mapIso ((systemIso).app k) ≪≫
    cmHarrisGeometricAssociatedCoefficientTrivializationAlong D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor
      q U ρ p m hm existence geometry hRigid k a

local notation "trivializationAlong" => cmHarrisGeometricCoefficientTrivializationAlong D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The forward trivialization is exactly the transported invariant evaluation. -/
@[simp] theorem cmHarrisGeometricCoefficientTrivializationAlong_hom
    (k : ℕᵒᵖ) {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj k) :
    ((trivializationAlong) k a).hom = (evaluationAlong) k a := rfl

/-- Evaluation retains every original full-lattice coefficient reduction. -/
@[reassoc] theorem cmHarrisGeometricCoefficientEvaluationAlong_transition
    {i j : ℕᵒᵖ} (f : i ⟶ j) {Z : (Xbar).Etale} (a : Z ⟶ (covers).obj.obj i) :
    (localizeOn Z).map ((pulledSystem).map f) ≫
        (evaluationAlong) j (a ≫ (covers).obj.map f) =
      (evaluationAlong) i a ≫ (localizeOn Z).map
        ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f)) := by
  dsimp only [cmHarrisGeometricCoefficientEvaluationAlong]
  rw [← Functor.map_comp_assoc, (systemIso).hom.naturality f,
    Functor.map_comp, Category.assoc,
    cmHarrisGeometricAssociatedCoefficientSystem_evaluationAlong]
  rw [Category.assoc]

/-- The existing inverse-image coefficient system at all exponents reachable
from k, localized on the exact geometric source cover at k. -/
def cmHarrisGeometricCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((Jbar).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  Under.forget k ⋙ pulledSystem ⋙ localizeOn ((covers).obj.obj k)

local notation "sourceSystem" => cmHarrisGeometricCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "associatedSource" => cmHarrisGeometricAssociatedCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "constantSource" => cmHarrisGeometricConstantCoefficientSourceSystem D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "associatedSourceTrivialization" =>
  cmHarrisGeometricAssociatedCoefficientSourceTrivialization D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid

/-- The actual source-local inverse-image diagram compares with association on
the same exact covers, by localization and restriction of the whole-system iso. -/
def cmHarrisGeometricCoefficientSourceAssociatedIso (k : ℕᵒᵖ) :
    (sourceSystem) k ≅ (associatedSource) k :=
  Functor.isoWhiskerLeft (Under.forget k)
    (Functor.isoWhiskerRight systemIso (localizeOn ((covers).obj.obj k)))

local notation "sourceIso" => cmHarrisGeometricCoefficientSourceAssociatedIso D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Every source component is the same localized inverse-image comparison. -/
@[simp] theorem cmHarrisGeometricCoefficientSourceAssociatedIso_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    ((sourceIso) k).hom.app i =
      (localizeOn ((covers).obj.obj k)).map ((systemIso).hom.app i.right) := rfl

/-- A single exact source cover simultaneously trivializes the entire reachable
inverse-image coefficient diagram with its original reduction maps. -/
def cmHarrisGeometricCoefficientSourceTrivialization (k : ℕᵒᵖ) :
    (sourceSystem) k ≅ (constantSource) k :=
  (sourceIso) k ≪≫ (associatedSourceTrivialization) k

local notation "sourceTrivialization" => cmHarrisGeometricCoefficientSourceTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- The source trivialization evaluates along the exact geometric forgetting map. -/
@[simp] theorem cmHarrisGeometricCoefficientSourceTrivialization_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    ((sourceTrivialization) k).hom.app i =
      (evaluationAlong) i.right ((covers).obj.map i.hom) := rfl

/-- The inverse reverses invariant evaluation and the same localized comparison. -/
@[simp] theorem cmHarrisGeometricCoefficientSourceTrivialization_inv_app
    (k : ℕᵒᵖ) (i : Under k) :
    ((sourceTrivialization) k).inv.app i =
      ((associatedSourceTrivialization) k).inv.app i ≫
        (localizeOn ((covers).obj.obj k)).map ((systemIso).inv.app i.right) := rfl

/-- The forward source trivialization changes every transition to the actual
constant sheaf of the original full-lattice reduction. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSourceTrivialization_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localizeOn ((covers).obj.obj k)).map ((pulledSystem).map f.right) ≫
        ((sourceTrivialization) k).hom.app j =
      ((sourceTrivialization) k).hom.app i ≫
        (localizeOn ((covers).obj.obj k)).map
          ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) :=
  ((sourceTrivialization) k).hom.naturality f

/-- The inverse source trivialization also respects every original reduction. -/
@[reassoc] theorem cmHarrisGeometricCoefficientSourceTrivialization_inv_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localizeOn ((covers).obj.obj k)).map
          ((constantSheaf Jbar (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) ≫
        ((sourceTrivialization) k).inv.app j =
      ((sourceTrivialization) k).inv.app i ≫
        (localizeOn ((covers).obj.obj k)).map ((pulledSystem).map f.right) :=
  ((sourceTrivialization) k).inv.naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
