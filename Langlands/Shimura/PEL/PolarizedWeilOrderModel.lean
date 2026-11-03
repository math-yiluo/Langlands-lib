import Langlands.AbelianScheme.IntegralOrderModelPolarization
import Langlands.AbelianScheme.PolarizedFiniteLevel.Data
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof
import Langlands.Shimura.PEL.PolarizedWeilIntegralClasses

/-! # Polarized rational actions on actual integral order models -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.PolarizedWeilLevel

open Langlands.AbelianScheme Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (P : Prerequisites.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S]
  {R : Type v} [Ring R] [Algebra ℚ R] [StarRing R]

local notation "PObj" => PolarizedAction P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality S R

/-- The selected actual dual witnesses already carried by a polarized action. -/
def PolarizedAction.dualWitness (X : PObj) : DualWitness X.actionObj.abelianScheme where
  hasDual := X.hasDual
  geometry := X.geometry
  inverseBundle := X.inversePoincare
  evaluation := X.evaluation

variable {O : Subalgebra ℤ R} [Submodule.IsLattice ℚ O.toSubmodule]
  {I : Type w} (b : Basis I ℤ O)
  (X : PolarizedAction P.preservation P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability P.square P.universality S R)
  (M : IntegralOrderModel (IntegralOrderExtension.restrict (O := O) X.actionObj.action))
  (W : DualWitness M.B)

local notation "α" => X.actionObj.action
local notation "β" => integralActionRationalExtension M.B b M.action
local notation "addAA" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  X.actionObj.abelianScheme X.actionObj.abelianScheme X.hasDual X.hasDual
local notation "addAB" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  X.actionObj.abelianScheme M.B X.hasDual W.hasDual
local notation "addBA" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  M.B X.actionObj.abelianScheme W.hasDual X.hasDual
local notation "addBB" => relativeDualSchemeMapAdditivity P.preservation P.stability S
  M.B M.B W.hasDual W.hasDual
local notation "pullLam" => IntegralOrderModel.dualPullbackHom α M P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  X.hasDual W.hasDual X.geometry W.geometry X.inversePoincare X.evaluation
  W.inverseBundle W.evaluation X.polarization

/-- The actual integral model carries a faithful rational action, geometric polarization,
and the full original involution equation over a characteristic-zero field scheme. -/
def PolarizedAction.orderModel
    {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K)) : PObj where
  actionObj := RationalAlgebraAction.of M.B β
  hasDual := W.hasDual
  geometry := W.geometry
  inversePoincare := W.inverseBundle
  evaluation := W.evaluation
  dualEndAdditivity := addBB
  polarization := pullLam
  isPolarization := IntegralOrderModel.dualPullback_isPolarization_overField α M
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability X.hasDual W.hasDual X.geometry W.geometry X.inversePoincare X.evaluation
    W.inverseBundle W.evaluation P.square P.universality addAA addBB p X.polarization
    X.isPolarization
  faithful := (IntegralOrderModel.rationalExtension_injective_iff b α M).mpr X.faithful
  involutionCompatible := IntegralOrderModel.dualPullback_involutionCompatible b α M
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability X.hasDual W.hasDual X.geometry W.geometry X.inversePoincare X.evaluation
    W.inverseBundle W.evaluation addAA addBA addBB X.polarization X.involutionCompatible

variable {K : Type u} [Field K] [CharZero K] (p : S ⟶ Spec (.of K))

local notation "Y" => PolarizedAction.orderModel P b X M W p

/-- The comparison retains the original actual forward map and its inverse multiple. -/
def PolarizedAction.orderModelIso : X.actionObj ≅ (Y).actionObj :=
  IntegralOrderModel.rationalAlgebraIso b α M

/-- The same model action is an integral restriction on the same polarized representative. -/
def PolarizedAction.orderModelRestriction :
    IntegralActionRestriction P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality O Y where
  action := M.action
  agrees x := (integralActionRationalExtension_coe M.B b M.action x).symm

omit [QuasiSeparatedSpace S] [Submodule.IsLattice ℚ O.toSubmodule] in
/-- The model comparison multiplier is positive in the original rational order. -/
theorem PolarizedAction.orderModelMultiple_pos : 0 < (M.inverseData.multiple : ℚ) ^ 2 :=
  sq_pos_of_ne_zero (Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero)

/-- The actual forward comparison has the exact positive square multiplier. -/
theorem PolarizedAction.orderModelMultiple
    (additivity : PairAdditivity P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability P.square P.universality (S := S) (D := R)) :
    Multiple P.preservation P.composition P.unitCoherence P.associativity P.comparison
      P.symmetry P.stability P.square P.universality additivity X Y
      (Units.mk0 ((M.inverseData.multiple : ℚ) ^ 2)
        (pow_ne_zero _ (Int.cast_ne_zero.mpr M.inverseData.multiple_ne_zero)))
      (PolarizedAction.orderModelIso P b X M W p) :=
  IntegralOrderModel.dualPullback_multiple α M P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability X.hasDual W.hasDual X.geometry
    W.geometry X.inversePoincare X.evaluation W.inverseBundle W.evaluation
    addAA addAB addBA X.polarization

end Langlands.Shimura.PEL.PolarizedWeilLevel
