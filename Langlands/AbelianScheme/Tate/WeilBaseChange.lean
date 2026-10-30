import Langlands.AlgebraicGeometry.Picard.FiniteWeilBaseChange
import Langlands.AbelianScheme.Tate.WeilRational
import Langlands.AbelianScheme.Tate.RationalBaseChange

/-! # Ground base change of integral and rational Weil pairings -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
set_option quotPrecheck false in
local notation "GAb" => dualCommGroupSchemeFromEvaluation ((baseChange b).obj A) hA'
  preservation MA' evaluationA' stability composition unitCoherence associativity comparison
  symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp GA
local notation "GDb" => Langlands.CommGroupScheme.toGrp GAb
local notation "dualLevel" => dualLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA'

/-- The canonical dual torsion comparison commutes with divisibility transitions. -/
theorem dualLevelBaseChange_transition (T : Over S') {n m : ℕ} (h : n ∣ m)
    (y : GroupScheme.Tate.Level GDb T m) :
    dualLevel T n (GroupScheme.Tate.transition GDb T h y) =
      GroupScheme.Tate.transition GD ((Over.map b).obj T) h (dualLevel T m y) := by
  let E := dualGrpBaseChangeIso b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA'
  change GroupScheme.Tate.levelBaseChange b GD T n
      (GroupScheme.Tate.levelMap T E.inv n (GroupScheme.Tate.transition GDb T h y)) =
    GroupScheme.Tate.transition GD ((Over.map b).obj T) h
      (GroupScheme.Tate.levelBaseChange b GD T m (GroupScheme.Tate.levelMap T E.inv m y))
  rw [GroupScheme.Tate.levelMap_transition, GroupScheme.Tate.levelBaseChange_transition]

/-- The inverse dual torsion comparison also commutes with transitions. -/
theorem dualLevelBaseChange_symm_transition (T : Over S') {n m : ℕ} (h : n ∣ m)
    (y : GroupScheme.Tate.Level GD ((Over.map b).obj T) m) :
    (dualLevel T n).symm (GroupScheme.Tate.transition GD ((Over.map b).obj T) h y) =
      GroupScheme.Tate.transition GDb T h ((dualLevel T m).symm y) := by
  apply (dualLevel T n).injective
  rw [AddEquiv.apply_symm_apply, dualLevelBaseChange_transition, AddEquiv.apply_symm_apply]

variable (T : Over S') (P : ℕ → Prop)

/-- Coordinatewise base change on the actual integral Tate module of the dual. -/
def dualIntegralBaseChange :
    GroupScheme.Tate.Integral GDb T P ≃+
      GroupScheme.Tate.Integral GD ((Over.map b).obj T) P where
  toFun y := ⟨fun n => dualLevel T n.val (y.val n), by
    intro n m h
    rw [← dualLevelBaseChange_transition, y.property n m h]⟩
  invFun y := ⟨fun n => (dualLevel T n.val).symm (y.val n), by
    intro n m h
    rw [← dualLevelBaseChange_symm_transition, y.property n m h]⟩
  left_inv y := by
    apply Subtype.ext
    funext n
    exact (dualLevel T n.val).symm_apply_apply (y.val n)
  right_inv y := by
    apply Subtype.ext
    funext n
    exact (dualLevel T n.val).apply_symm_apply (y.val n)
  map_add' y z := by
    apply Subtype.ext
    funext n
    exact (dualLevel T n.val).map_add (y.val n) (z.val n)

local notation "dualIntegral" => dualIntegralBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
  hA' MA' evaluationA'

@[simp] theorem evaluation_dualIntegralBaseChange (n : GroupScheme.Tate.Index P)
    (y : GroupScheme.Tate.Integral GDb T P) :
    GroupScheme.Tate.evaluation GD ((Over.map b).obj T) P n (dualIntegral T P y) =
      dualLevel T n.val (GroupScheme.Tate.evaluation GDb T P n y) := rfl

@[simp] theorem evaluation_dualIntegralBaseChange_symm (n : GroupScheme.Tate.Index P)
    (y : GroupScheme.Tate.Integral GD ((Over.map b).obj T) P) :
    GroupScheme.Tate.evaluation GDb T P n ((dualIntegral T P).symm y) =
      (dualLevel T n.val).symm
        (GroupScheme.Tate.evaluation GD ((Over.map b).obj T) P n y) := rfl

theorem continuous_dualIntegralBaseChange : Continuous (dualIntegral T P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := dualLevel T n.val)).comp
    (GroupScheme.Tate.continuous_evaluation GDb T P n)

theorem continuous_dualIntegralBaseChange_symm : Continuous (dualIntegral T P).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := (dualLevel T n.val).symm)).comp
    (GroupScheme.Tate.continuous_evaluation GD ((Over.map b).obj T) P n)

theorem dualIntegralBaseChange_smul (a : Global.ProfiniteIntegerRing)
    (y : GroupScheme.Tate.Integral GDb T P) :
    dualIntegral T P (a • y) = a • dualIntegral T P y := by
  apply Subtype.ext
  funext n
  exact ZMod.map_smul (dualLevel T n.val).toAddMonoidHom
    (GroupScheme.Tate.fullReduction P n a) (y.val n)

/-- The dual comparison is a continuous equivalence over the full residue ring. -/
def dualIntegralBaseChangeLinearEquiv :
    GroupScheme.Tate.Integral GDb T P ≃L[Global.ProfiniteIntegerRing]
      GroupScheme.Tate.Integral GD ((Over.map b).obj T) P where
  __ := dualIntegral T P
  map_smul' := dualIntegralBaseChange_smul b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA' T P
  continuous_toFun := continuous_dualIntegralBaseChange b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
    hA' MA' evaluationA' T P
  continuous_invFun := continuous_dualIntegralBaseChange_symm b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
    hA' MA' evaluationA' T P

theorem dualIntegralBaseChange_away_smul (m : ℕ)
    (a : Global.PrimeToProfiniteIntegerRing m) (y : GroupScheme.Tate.Away GDb T m) :
    dualIntegral T (fun n => Nat.Coprime n m) (a • y) =
      a • dualIntegral T (fun n => Nat.Coprime n m) y := by
  apply Subtype.ext
  funext n
  exact ZMod.map_smul (dualLevel T n.val).toAddMonoidHom
    (GroupScheme.Tate.awayReduction m n a) (y.val n)

/-- The same dual comparison over the actual away residue ring. -/
def dualAwayBaseChangeLinearEquiv (m : ℕ) :
    GroupScheme.Tate.Away GDb T m ≃L[Global.PrimeToProfiniteIntegerRing m]
      GroupScheme.Tate.Away GD ((Over.map b).obj T) m where
  __ := dualIntegral T (fun n => Nat.Coprime n m)
  map_smul' := dualIntegralBaseChange_away_smul b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA' T m
  continuous_toFun := continuous_dualIntegralBaseChange b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
    hA' MA' evaluationA' T _
  continuous_invFun := continuous_dualIntegralBaseChange_symm b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
    hA' MA' evaluationA' T _

/-- Rationalization over the integers of the canonical dual comparison. -/
def dualRationalBaseChange :
    GroupScheme.Tate.Rational GDb T P ≃ₗ[ℚ]
      GroupScheme.Tate.Rational GD ((Over.map b).obj T) P :=
  (dualIntegral T P).toIntLinearEquiv.baseChange ℤ ℚ _ _

local notation "dualRational" => dualRationalBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA MA evaluationA
  hA' MA' evaluationA'

@[simp] theorem dualRationalBaseChange_tmul (q : ℚ)
    (y : GroupScheme.Tate.Integral GDb T P) :
    dualRational T P (q ⊗ₜ[ℤ] y) = q ⊗ₜ[ℤ] dualIntegral T P y := rfl

@[simp] theorem dualRationalBaseChange_symm_tmul (q : ℚ)
    (y : GroupScheme.Tate.Integral GD ((Over.map b).obj T) P) :
    (dualRational T P).symm (q ⊗ₜ[ℤ] y) = q ⊗ₜ[ℤ] (dualIntegral T P).symm y := rfl

variable {P}

/-- Restricting the selected orders commutes with integral dual base change. -/
theorem dualIntegralBaseChange_restrictAway (m : ℕ) (y : GroupScheme.Tate.Full GDb T) :
    dualIntegral T (fun n => Nat.Coprime n m) (GroupScheme.Tate.restrictAway GDb T m y) =
      GroupScheme.Tate.restrictAway GD ((Over.map b).obj T) m
        (dualIntegral T (fun _ => True) y) := rfl

/-- Restricting the selected orders commutes with rational dual base change. -/
theorem dualRationalBaseChange_restrictAway (m : ℕ)
    (y : GroupScheme.Tate.RationalFull GDb T) :
    dualRational T (fun n => Nat.Coprime n m)
        (GroupScheme.Tate.rationalRestrictAway GDb T m y) =
      GroupScheme.Tate.rationalRestrictAway GD ((Over.map b).obj T) m
        (dualRational T (fun _ => True) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul q y => rfl
  | add y z hy hz => simp_all

variable (P)

/-- The same full finite-adele comparison is used on both dual modules. -/
def dualFiniteAdeleBaseChange (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := GroupScheme.Tate.finiteAdeleModule GDb T P h
    let := GroupScheme.Tate.finiteAdeleModule GD ((Over.map b).obj T) P h
    GroupScheme.Tate.Rational GDb T P ≃ₗ[Global.FiniteAdeles ℚ]
      GroupScheme.Tate.Rational GD ((Over.map b).obj T) P := by
  let := GroupScheme.Tate.finiteAdeleModule GDb T P h
  let := GroupScheme.Tate.finiteAdeleModule GD ((Over.map b).obj T) P h
  exact { (dualRational T P).toEquiv with
    map_add' := (dualRational T P).map_add
    map_smul' := fun a y => TateScalarExtension.map_action
      (dualIntegralBaseChangeLinearEquiv b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
        evaluationA' T P).toLinearEquiv.toLinearMap _ y }

/-- The coupled away comparison is likewise shared at both endpoints. -/
def dualPrimeToFiniteAdeleBaseChange {h : Global.RationalProfiniteIntegerAdeleComparison}
    {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := GroupScheme.Tate.primeToFiniteAdeleModule GDb T hAway
    let := GroupScheme.Tate.primeToFiniteAdeleModule GD ((Over.map b).obj T) hAway
    GroupScheme.Tate.RationalAway GDb T m ≃ₗ[Global.PrimeToFiniteAdeles m]
      GroupScheme.Tate.RationalAway GD ((Over.map b).obj T) m := by
  let := GroupScheme.Tate.primeToFiniteAdeleModule GDb T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule GD ((Over.map b).obj T) hAway
  exact { (dualRational T (fun n => Nat.Coprime n m)).toEquiv with
    map_add' := (dualRational T (fun n => Nat.Coprime n m)).map_add
    map_smul' := fun a y => TateScalarExtension.map_action
      (dualAwayBaseChangeLinearEquiv b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
        evaluationA' T m).toLinearEquiv.toLinearMap _ y }

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace S']
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})

/-- Base change preserves the intrinsic integral Weil value in the same actual twist. -/
theorem integralWeilValue_baseChange
    (x : GroupScheme.Tate.Integral ((baseChange b).obj A).toGrp T P)
    (y : GroupScheme.Tate.Integral GDb T P) :
    integralWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA' MA' evaluationA' compatibility T P x y =
      integralWeilValue preservation composition unitCoherence associativity comparison symmetry
        stability hA MA evaluationA compatibility ((Over.map b).obj T) P
        (GroupScheme.Tate.integralBaseChange b A.toGrp T P x) (dualIntegral T P y) := by
  apply Subtype.ext
  funext n
  exact finiteWeilLevelBilinearMap_baseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA MA evaluationA hA' MA'
    evaluationA' n.val T (x.val n) (y.val n)

/-- Rational base change preserves the Weil pairing without trivializing its twist. -/
theorem rationalWeilBilinearMap_baseChange
    (x : GroupScheme.Tate.Rational ((baseChange b).obj A).toGrp T P)
    (y : GroupScheme.Tate.Rational GDb T P) :
    rationalWeilBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA' MA' evaluationA' compatibility T P x y =
      rationalWeilBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA compatibility ((Over.map b).obj T) P
        (GroupScheme.Tate.rationalBaseChange b A.toGrp T P x) (dualRational T P y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      change rationalWeilBilinearMap preservation composition unitCoherence associativity
          comparison symmetry stability hA' MA' evaluationA' compatibility T P
          (q ⊗ₜ[ℤ] x) (r ⊗ₜ[ℤ] y) =
        rationalWeilBilinearMap preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA compatibility ((Over.map b).obj T) P
          (q ⊗ₜ[ℤ] GroupScheme.Tate.integralBaseChange b A.toGrp T P x)
          (r ⊗ₜ[ℤ] dualIntegral T P y)
      rw [rationalWeilBilinearMap_tmul, rationalWeilBilinearMap_tmul]
      exact congrArg (fun w => (q * r) ⊗ₜ[ℤ] w)
        (integralWeilValue_baseChange b A preservation composition unitCoherence associativity
          comparison symmetry stability universality hA MA evaluationA hA' MA' evaluationA'
          T P compatibility x y)
    | add y z hy hz =>
      simp only [map_add, hy, hz]
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz]

end Langlands.AbelianScheme
