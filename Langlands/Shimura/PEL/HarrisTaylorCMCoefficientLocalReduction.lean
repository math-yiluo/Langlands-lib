import Langlands.Shimura.PEL.HarrisTaylorCMCoefficientSourceTrivialization
import Langlands.Shimura.Coefficients.CrossCoverEvaluation
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Simultaneous local models for original CM coefficient reductions -/

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
local notation "Rcoeff" => HarrisCoefficientIntegers K p
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

local notation "constant" k =>
  (constantSheaf J (ModuleCat.{0} Rcoeff)).obj ((coefficients).obj.obj k)
local notation "constantAction" k =>
  ((constantSheaf J (ModuleCat.{0} Rcoeff)).mapAction
    ((cmHarrisCoefficientGroups D ρ p U m hm).obj k)).obj ((coefficients).action k)
local notation "localize" k =>
  (J).overPullback (ModuleCat.{0} Rcoeff) ((covers).obj.obj k)
local notation "inc" => cmHarrisCoefficientSystemInclusion D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid
local notation "trivialization" => cmHarrisCoefficientSystemTrivialization D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- Evaluate the original coefficient sheaf along the actual fine-to-coarse cover map. -/
def cmHarrisCoefficientSystemTrivializationAlong {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (localize i).obj ((system).obj j) ≅ (localize i).obj (constant j) :=
  (associatedTrivializationAlongOfSplitting J ((covers).action j) ((covers).obj.map f)
    (etaleTorsorSectionSplitting X _ ((covers).action j) (coverProperty j) Rcoeff)).app
      (constantAction j)

local notation "along" => cmHarrisCoefficientSystemTrivializationAlong D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
  existence geometry hRigid

/-- This is independently constructed graph evaluation on the original cover. -/
theorem cmHarrisCoefficientSystemTrivializationAlong_hom {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (along f).hom =
      (localize i).map (inc j) ≫
        productEvaluationAlong J ((covers).obj.map f) (constant j) := rfl

/-- At the identity arrow this is the previously constructed original-cover trivialization. -/
@[simp] theorem cmHarrisCoefficientSystemTrivializationAlong_id (i : ℕᵒᵖ) :
    along (𝟙 i) = trivialization i := by
  apply Iso.ext
  change associatedEvaluationAlong J ((covers).action i) ((covers).obj.map (𝟙 i))
    (constantAction i) = associatedEvaluation J ((covers).action i) (constantAction i)
  rw [CategoryTheory.Functor.map_id]
  exact associatedEvaluationAlong_id J ((covers).action i) (constantAction i)

/-- Original transitions become the actual constant lattice reductions on the fine cover. -/
@[reassoc] theorem cmHarrisCoefficientSystem_map_evaluation {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (localize i).map ((system).map f) ≫ (along f).hom =
      (trivialization i).hom ≫
        (localize i).map ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
          ((coefficients).obj.map f)) := by
  have hi := cmHarrisCoefficientSystem_map_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f
  have hmapped := congrArg (fun a => (localize i).map a) hi
  simp only [Functor.map_comp] at hmapped
  change (localize i).map ((system).map f) ≫
      ((localize i).map (inc j) ≫
        productEvaluationAlong J ((covers).obj.map f) (constant j)) =
    ((localize i).map (inc i) ≫ productEvaluation J ((covers).action i) (constant i)) ≫ _
  rw [← coverPullback_productEvaluation J ((covers).action i)
    ((covers).obj.map f) (constant j)]
  calc
    _ = ((localize i).map (inc i) ≫
        (localize i).map ((productSheaf J ((covers).obj.obj i)).map
          ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
            ((coefficients).obj.map f)))) ≫
        productEvaluation J ((covers).action i) (constant j) := by
      convert congrArg
        (fun a => a ≫ productEvaluation J ((covers).action i) (constant j)) hmapped
        using 1
      simp only [Category.assoc]
      rfl
    _ = _ := by
      rw [Category.assoc]
      exact (congrArg (fun a => (localize i).map (inc i) ≫ a)
        (productEvaluation_natural J ((covers).action i)
          ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
            ((coefficients).obj.map f)))).trans (Category.assoc _ _ _).symm

private theorem cmCoverPullback_evaluationAlong {k i j : ℕᵒᵖ}
    (a : k ⟶ i) (f : i ⟶ j) :
    (localize k).map (coverPullback J ((covers).obj.map f) (constant j)) ≫
        productEvaluationAlong J ((covers).obj.map a) (constant j) =
      productEvaluationAlong J ((covers).obj.map (a ≫ f)) (constant j) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext T
  change (constant j).obj.map
      (prod.map ((covers).obj.map f) (𝟙 T.unop.left)).op ≫
        (constant j).obj.map
          (prod.lift (T.unop.hom ≫ (covers).obj.map a) (𝟙 T.unop.left)).op =
    (constant j).obj.map
      (prod.lift (T.unop.hom ≫ (covers).obj.map (a ≫ f)) (𝟙 T.unop.left)).op
  rw [← CategoryTheory.Functor.map_comp, ← op_comp]
  congr 2
  apply prod.hom_ext <;> simp [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Every original transition becomes coefficient reduction on any common finer cover. -/
@[reassoc] theorem cmHarrisCoefficientSystem_map_evaluationAlong {k i j : ℕᵒᵖ}
    (a : k ⟶ i) (f : i ⟶ j) :
    (localize k).map ((system).map f) ≫ (along (a ≫ f)).hom =
      (along a).hom ≫
        (localize k).map ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
          ((coefficients).obj.map f)) := by
  have hi := cmHarrisCoefficientSystem_map_inclusion D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid f
  have hmapped := congrArg (fun b => (localize k).map b) hi
  simp only [CategoryTheory.Functor.map_comp] at hmapped
  change (localize k).map ((system).map f) ≫
      ((localize k).map (inc j) ≫
        productEvaluationAlong J ((covers).obj.map (a ≫ f)) (constant j)) =
    ((localize k).map (inc i) ≫
      productEvaluationAlong J ((covers).obj.map a) (constant i)) ≫ _
  rw [← cmCoverPullback_evaluationAlong D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid a f]
  calc
    _ = ((localize k).map (inc i) ≫
        (localize k).map ((productSheaf J ((covers).obj.obj i)).map
          ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
            ((coefficients).obj.map f)))) ≫
        productEvaluationAlong J ((covers).obj.map a) (constant j) := by
      simpa only [Category.assoc] using congrArg
        (fun b => b ≫ productEvaluationAlong J ((covers).obj.map a) (constant j)) hmapped
    _ = _ := by
      rw [Category.assoc]
      exact (congrArg (fun b => (localize k).map (inc i) ≫ b)
        (productEvaluationAlong_natural J ((covers).obj.map a)
          ((constantSheaf J (ModuleCat.{0} Rcoeff)).map
            ((coefficients).obj.map f)))).trans (Category.assoc _ _ _).symm

/-- On the original cover at `k`, all coefficient stages below `k` form the actual
constant reduction diagram, via the independently constructed graph evaluations. -/
def cmHarrisCoefficientSystemLocalDiagramIso (k : ℕᵒᵖ) :
    ((Under.forget k ⋙ system) ⋙ localize k) ≅
      ((Under.forget k ⋙ (coefficients).obj ⋙
        constantSheaf J (ModuleCat.{0} Rcoeff)) ⋙ localize k) :=
  cmHarrisCoefficientSourceTrivialization D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid k

/-- Each component is the independent original-cover graph evaluation. -/
@[simp] theorem cmHarrisCoefficientSystemLocalDiagramIso_app (k : ℕᵒᵖ)
    (a : Under k) :
    (cmHarrisCoefficientSystemLocalDiagramIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k).app a = along a.hom := rfl

/-- The component at the identity arrow is the original stage's trivialization. -/
@[simp] theorem cmHarrisCoefficientSystemLocalDiagramIso_app_id (k : ℕᵒᵖ) :
    (cmHarrisCoefficientSystemLocalDiagramIso D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid k).app (Under.mk (𝟙 k)) = trivialization k :=
  cmHarrisCoefficientSystemTrivializationAlong_id D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
    existence geometry hRigid k

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
