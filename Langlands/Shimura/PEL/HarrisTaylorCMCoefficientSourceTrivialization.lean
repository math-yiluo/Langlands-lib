import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientScalars
import Langlands.Shimura.Coefficients.VaryingCoverLocalTrivialization

/-! # Compatible original CM coefficient diagrams on a fixed source cover -/

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

local notation "schemes" => cmSchemeTower D C preservation composition
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

local notation "X" => Functor.obj (schemes q) U
local notation "J" => Scheme.smallEtaleTopology X
local notation "R" => HarrisCoefficientIntegers K p
local notation "coefficients" => cmHarrisCoefficientDiagram D ρ p U m hm
local notation "covers" => cmHarrisCoefficientEtaleDiagram D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "coverProperty" => cmHarrisCoefficientEtaleDiagram_isFiniteGeometricTorsor
  D C preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor
  q U ρ p m hm existence geometry hRigid
local notation "torsor" k => cmHarrisCoefficientTorsor D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k

local notation "system" => cmHarrisCoefficientSystem D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "quotientAction" k => cmHarrisCoefficientAction D ρ p U m hm k
local notation "quotientSheaf" k => cmHarrisCoefficientSheaf D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "quotientInclusion" k => cmHarrisCoefficientInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U existence geometry hRigid
  ρ p m hm k
local notation "systemInclusion" k => cmHarrisCoefficientSystemInclusion D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid k
local notation "quotientMap" k => Ideal.Quotient.mk (harrisCoefficientScalarIdeal K p m ^ k)


local notation "sheafComparison" k => cmHarrisCoefficientSheafRestrictIso D C
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k
local notation "constantComparison" k =>
  (constantRestrictScalarsIso J (quotientMap k)).app (quotientAction k).V


local notation "restrictedSystem" => cmHarrisRestrictedCoefficientSystem D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "systemComparison" => cmHarrisRestrictedCoefficientSystemIso D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "localizeOn" Z => (J).overPullback (ModuleCat.{0} R) Z
local notation "restrictOn" k:arg Z:arg => sheafCompose ((J).over Z)
  (ModuleCat.restrictScalars.{0} (quotientMap k))
local notation "quotientConstantAction" k =>
  ((constantSheaf J (ModuleCat.{0} (R ⧸ harrisCoefficientScalarIdeal K p m ^ k))).mapAction
    (SmallCMResidualGroup D U (cmHarrisCoefficientLevel D ρ p U m hm k))).obj
      (quotientAction k)

/-- The original quotient-ring invariant evaluation along a map into its cover,
restricted to integral scalars and followed by the canonical constant comparison. -/
def cmHarrisRestrictedCoefficientEvaluationAlong (k : ℕ)
    {Z : (X).Etale} (a : Z ⟶ (torsor k).val.V) :
    (localizeOn Z).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj
          (quotientSheaf k)) ⟶
      (localizeOn Z).obj
        ((constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj (op k))) :=
  (restrictOn k Z).map
      (associatedEvaluationAlong J (torsor k).val a (quotientConstantAction k)) ≫
    (localizeOn Z).map (constantComparison k).hom

local notation "restrictedEvaluation" k:arg a:arg => cmHarrisRestrictedCoefficientEvaluationAlong D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k a

/-- The scalar comparison preserves original evaluation along every actual map
into the coefficient cover. -/
@[reassoc] theorem cmHarrisCoefficientSheafRestrictIso_hom_evaluationAlong
    (k : ℕ) {Z : (X).Etale} (a : Z ⟶ (torsor k).val.V) :
    (localizeOn Z).map (sheafComparison k).hom ≫
        etaleAssociatedEvaluationAlong X covers coefficients (op k) a =
      restrictedEvaluation k a := by
  let loc := localizeOn Z
  let c := (constantComparison k).hom
  let F := (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).obj
    ((constantSheaf J
      (ModuleCat.{0} (R ⧸ harrisCoefficientScalarIdeal K p m ^ k))).obj
        (quotientAction k).V)
  let F' := (constantSheaf J (ModuleCat.{0} R)).obj ((coefficients).obj.obj (op k))
  let b := (sheafCompose J (ModuleCat.restrictScalars.{0} (quotientMap k))).map
    (quotientInclusion k)
  have hi := cmHarrisCoefficientSheafRestrictIso_hom_inclusion D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k
  have hi' := congrArg (fun f => loc.map f) hi
  have hi'' := ((loc.map_comp _ _).symm.trans hi').trans (loc.map_comp _ _)
  have hn := productEvaluationAlong_natural J a c
  change loc.map (sheafComparison k).hom ≫
      (loc.map (systemInclusion (op k)) ≫ productEvaluationAlong J a F') = _
  calc
    _ = (loc.map (sheafComparison k).hom ≫ loc.map (systemInclusion (op k))) ≫
        productEvaluationAlong J a F' := (Category.assoc _ _ _).symm
    _ = (loc.map b ≫ loc.map ((productSheaf J (torsor k).val.V).map c)) ≫
        productEvaluationAlong J a F' :=
      congrArg (fun f => f ≫ productEvaluationAlong J a F') hi''
    _ = loc.map b ≫ (loc.map ((productSheaf J (torsor k).val.V).map c) ≫
        productEvaluationAlong J a F') := Category.assoc _ _ _
    _ = loc.map b ≫ (productEvaluationAlong J a F ≫ loc.map c) :=
      congrArg (fun f => loc.map b ≫ f) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The integral CM coefficient diagram through k, localized on its original cover. -/
def cmHarrisCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  Under.forget k ⋙ (system) ⋙ localizeOn ((covers).obj.obj k)

/-- The original full-lattice reductions, formed as constant sheaves on J
and localized on the same fixed cover. -/
def cmHarrisConstantCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  etaleConstantSourceSystem X covers k coefficients

/-- Original invariant evaluation compatibly trivializes the whole integral
CM coefficient diagram through the chosen exponent. -/
def cmHarrisCoefficientSourceTrivialization (k : ℕᵒᵖ) :
    cmHarrisCoefficientSourceSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k ≅
    cmHarrisConstantCoefficientSourceSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k :=
  etaleAssociatedSourceTrivialization X covers coverProperty k coefficients

local notation "integralSourceTrivialization" k => cmHarrisCoefficientSourceTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- Every integral component is invariant evaluation along its original
CM forgetting map from the fixed source cover. -/
@[simp] theorem cmHarrisCoefficientSourceTrivialization_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (integralSourceTrivialization k).hom.app i =
      etaleAssociatedEvaluationAlong X covers coefficients i.right
        ((covers).obj.map i.hom) := rfl

/-- Integral transition maps become the original full-lattice reductions
under the simultaneous evaluation trivialization. -/
@[reassoc] theorem cmHarrisCoefficientSourceTrivialization_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localizeOn ((covers).obj.obj k)).map ((system).map f.right) ≫
        (integralSourceTrivialization k).hom.app j =
      (integralSourceTrivialization k).hom.app i ≫
        (localizeOn ((covers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) :=
  (integralSourceTrivialization k).hom.naturality f

/-- The original quotient-ring sheaf system, restricted to integral scalars,
on the fixed original coefficient cover through exponent k. -/
def cmHarrisRestrictedCoefficientSourceSystem (k : ℕᵒᵖ) :
    Under k ⥤ Sheaf ((J).over ((covers).obj.obj k)) (ModuleCat.{0} R) :=
  Under.forget k ⋙ (restrictedSystem) ⋙ localizeOn ((covers).obj.obj k)

/-- A simultaneous trivialization of the restricted original quotient-ring
sheaves with exactly the original full-lattice reduction transitions. -/
def cmHarrisRestrictedCoefficientSourceTrivialization (k : ℕᵒᵖ) :
    cmHarrisRestrictedCoefficientSourceSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k ≅
    cmHarrisConstantCoefficientSourceSystem D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k :=
  Functor.isoWhiskerLeft (Under.forget k)
    (Functor.isoWhiskerRight (systemComparison) (localizeOn ((covers).obj.obj k))) ≪≫
    cmHarrisCoefficientSourceTrivialization D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k

local notation "sourceTrivialization" k => cmHarrisRestrictedCoefficientSourceTrivialization D C
  preservation composition unitCoherence associativity comparison symmetry stability square
  universality dualityNaturality polarizationStability compatibility h htor q U
  ρ p m hm existence geometry hRigid k

/-- Every simultaneous-trivialization component is the restricted original
quotient-ring evaluation along the actual CM forgetting map. -/
@[simp] theorem cmHarrisRestrictedCoefficientSourceTrivialization_hom_app
    (k : ℕᵒᵖ) (i : Under k) :
    (sourceTrivialization k).hom.app i =
      restrictedEvaluation i.right.unop ((covers).obj.map i.hom) :=
  cmHarrisCoefficientSheafRestrictIso_hom_evaluationAlong D C preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid i.right.unop ((covers).obj.map i.hom)

/-- On the fixed finer cover, every original sheaf transition becomes the
actual full-lattice coefficient reduction. -/
@[reassoc] theorem cmHarrisRestrictedCoefficientSourceTrivialization_transition
    (k : ℕᵒᵖ) {i j : Under k} (f : i ⟶ j) :
    (localizeOn ((covers).obj.obj k)).map ((restrictedSystem).map f.right) ≫
        (sourceTrivialization k).hom.app j =
      (sourceTrivialization k).hom.app i ≫
        (localizeOn ((covers).obj.obj k)).map
          ((constantSheaf J (ModuleCat.{0} R)).map ((coefficients).obj.map f.right)) :=
  (sourceTrivialization k).hom.naturality f

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
