import Langlands.AlgebraicGeometry.Picard.FiniteWeilBilinearity
import Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionStatement
import Langlands.AbelianScheme.Tate.TwistDivisibility

/-! # The actual integral Weil pairing, conditional on relative transition compatibility -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

private lemma continuous_tateLevelEvaluationPair {S : Scheme.{u}}
    (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X]
    (T : Over S) (P : ℕ → Prop) (n : GroupScheme.Tate.Index P)
    {C : Type*} [TopologicalSpace C]
    (f : GroupScheme.Tate.Level G T n.val → GroupScheme.Tate.Level H T n.val → C) :
    Continuous (fun z : GroupScheme.Tate.Integral G T P ×
      GroupScheme.Tate.Integral H T P => f (z.1.val n) (z.2.val n)) :=
  (continuous_of_discreteTopology
    (f := fun z : GroupScheme.Tate.Level G T n.val ×
      GroupScheme.Tate.Level H T n.val => f z.1 z.2)).comp
        (((GroupScheme.Tate.continuous_evaluation G T P n).comp continuous_fst).prodMk
          ((GroupScheme.Tate.continuous_evaluation H T P n).comp continuous_snd))

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp GA
local notation "beta" => finiteWeilBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "pairing" => finiteWeilPairing preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

/-- The existing actual finite Weil pairing, on the torsion-section and root-of-unity levels. -/
def finiteWeilLevelBilinearMap (n : ℕ) (T : Over S) :
    GroupScheme.Tate.Level A.toGrp T n →+
      GroupScheme.Tate.Level GD T n →+ TateTwist.Level Γ(T.left, ⊤) n where
  toFun x := (mu.pointsLevelEquiv n T).toAddMonoidHom.comp
    ((beta n T ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm x)).comp
      (GroupScheme.Tate.kernelLevelEquiv GD T n).symm.toAddMonoidHom)
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change mu.pointsLevelEquiv n T
      (beta n T ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm 0)
        ((GroupScheme.Tate.kernelLevelEquiv GD T n).symm y)) = 0
    rw [map_zero, map_zero, AddMonoidHom.zero_apply, map_zero]
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    change mu.pointsLevelEquiv n T
      (beta n T ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm (x + x'))
        ((GroupScheme.Tate.kernelLevelEquiv GD T n).symm y)) = _
    simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.comp_apply]
    rfl

local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

/-- Its value is precisely the original scheme pairing evaluated at the actual kernel lifts. -/
lemma finiteWeilLevelBilinearMap_apply (n : ℕ) (T : Over S)
    (x : GroupScheme.Tate.Level A.toGrp T n) (y : GroupScheme.Tate.Level GD T n) :
    levelPair n T x y = mu.pointsLevelEquiv n T (Additive.ofMul
      (prod.lift (GroupScheme.Tate.kernelLift A.toGrp T n x)
        (GroupScheme.Tate.kernelLift GD T n y) ≫ pairing n)) := by
  rw [finiteWeilPairing_points]
  rfl

/-- The named relative theorem implies compatibility on actual torsion and root levels. -/
lemma finiteWeilLevelBilinearMap_transition
    (compatibility : RelativeFiniteWeilTransitionStatement.{u})
    (T : Over S) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n ∣ m)
    (x : GroupScheme.Tate.Level A.toGrp T m) (y : GroupScheme.Tate.Level GD T m) :
    TateTwist.transition Γ(T.left, ⊤) h (levelPair m T x y) =
      levelPair n T (GroupScheme.Tate.transition A.toGrp T h x)
        (GroupScheme.Tate.transition GD T h y) := by
  obtain ⟨x, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp T m).surjective x
  obtain ⟨y, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv GD T m).surjective y
  rw [← GroupScheme.Tate.kernelLevelEquiv_transition,
    ← GroupScheme.Tate.kernelLevelEquiv_transition]
  have hc := congrArg (fun q => prod.lift x.toMul y.toMul ≫ q)
    (compatibility preservation composition unitCoherence associativity comparison
      symmetry stability S A hA MA evaluationA n m hn hm h)
  have hp :
      prod.lift (x.toMul ≫ GroupScheme.Tate.kernelTransition A.toGrp h)
          (y.toMul ≫ GroupScheme.Tate.kernelTransition GD h) ≫ pairing n =
        (prod.lift x.toMul y.toMul ≫ pairing m) ≫
          (Langlands.CommGroupScheme.groupHom (mu.transition S h)).hom.hom := by
    rw [← Category.assoc, prod.lift_map] at hc
    simpa only [Category.assoc] using hc
  simp only [finiteWeilLevelBilinearMap_apply, GroupScheme.Tate.kernelLift,
    AddEquiv.symm_apply_apply]
  rw [← mu.pointsLevelEquiv_transition, ← hp]
  rfl

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (T : Over S) (P : ℕ → Prop)

/-- Coordinatewise evaluation gives a coherent family of actual roots of unity. -/
def integralWeilValue (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    TateTwist.Divisibility.Integral Γ(T.left, ⊤) P :=
  ⟨fun n => levelPair n.val T (x.val n) (y.val n), by
    intro n m h
    rw [finiteWeilLevelBilinearMap_transition preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA compatibility
      T n.property.1 m.property.1 h, x.property n m h, y.property n m h]⟩

local notation "limitPair" => integralWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T P

/-- The coordinate formula fixes the normalization without any roots-of-unity basis. -/
@[simp]
lemma evaluation_integralWeilValue (n : GroupScheme.Tate.Index P)
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n (limitPair x y) =
      levelPair n.val T (GroupScheme.Tate.evaluation A.toGrp T P n x)
        (GroupScheme.Tate.evaluation GD T P n y) := rfl

/-- Bilinearity over the actual full profinite-integer scalar ring. -/
def integralWeilBilinearMap :
    GroupScheme.Tate.Integral A.toGrp T P →ₗ[Global.ProfiniteIntegerRing]
      GroupScheme.Tate.Integral GD T P →ₗ[Global.ProfiniteIntegerRing]
        TateTwist.Divisibility.Integral Γ(T.left, ⊤) P where
  toFun x :=
    { toFun := limitPair x
      map_add' y y' := by
        apply Subtype.ext
        funext n
        exact map_add (levelPair n.val T (x.val n)) (y.val n) (y'.val n)
      map_smul' a y := by
        apply Subtype.ext
        funext n
        exact ZMod.map_smul (levelPair n.val T (x.val n))
          (GroupScheme.Tate.fullReduction P n a) (y.val n) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    exact DFunLike.congr_fun (map_add (levelPair n.val T) (x.val n) (x'.val n)) (y.val n)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    let f : GroupScheme.Tate.Level A.toGrp T n.val →+
        TateTwist.Level Γ(T.left, ⊤) n.val :=
      { toFun := fun z => levelPair n.val T z (y.val n)
        map_zero' := by rw [map_zero, AddMonoidHom.zero_apply]
        map_add' z z' := DFunLike.congr_fun
          (map_add (levelPair n.val T) z z') (y.val n) }
    exact ZMod.map_smul f
      (GroupScheme.Tate.fullReduction P n a) (x.val n)

@[simp]
lemma integralWeilBilinearMap_apply
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    integralWeilBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA compatibility T P x y = limitPair x y :=
  rfl

local notation "awayPair" p:arg => integralWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T
    (fun n => Nat.Coprime n p)

/-- The same prime-to-p value is bilinear over the actual prime-to-p scalar ring. -/
def awayWeilBilinearMap (p : ℕ) :
    GroupScheme.Tate.Away A.toGrp T p →ₗ[Global.PrimeToProfiniteIntegerRing p]
      GroupScheme.Tate.Away GD T p →ₗ[Global.PrimeToProfiniteIntegerRing p]
        TateTwist.Divisibility.Away Γ(T.left, ⊤) p where
  toFun x :=
    { toFun := (awayPair p) x
      map_add' y y' := by
        apply Subtype.ext
        funext n
        exact map_add (levelPair n.val T (x.val n)) (y.val n) (y'.val n)
      map_smul' a y := by
        apply Subtype.ext
        funext n
        exact ZMod.map_smul (levelPair n.val T (x.val n))
          (GroupScheme.Tate.awayReduction p n a) (y.val n) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    exact DFunLike.congr_fun (map_add (levelPair n.val T) (x.val n) (x'.val n)) (y.val n)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    let f : GroupScheme.Tate.Level A.toGrp T n.val →+
        TateTwist.Level Γ(T.left, ⊤) n.val :=
      { toFun := fun z => levelPair n.val T z (y.val n)
        map_zero' := by rw [map_zero, AddMonoidHom.zero_apply]
        map_add' z z' := DFunLike.congr_fun
          (map_add (levelPair n.val T) z z') (y.val n) }
    exact ZMod.map_smul f
      (GroupScheme.Tate.awayReduction p n a) (x.val n)

@[simp]
lemma awayWeilBilinearMap_apply (p : ℕ)
    (x : GroupScheme.Tate.Away A.toGrp T p) (y : GroupScheme.Tate.Away GD T p) :
    awayWeilBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA compatibility T p x y = (awayPair p) x y :=
  rfl

/-- Restricting the full pairing agrees with pairing the restricted actual torsion families. -/
lemma restrictAway_integralWeilValue (p : ℕ)
    (x : GroupScheme.Tate.Full A.toGrp T) (y : GroupScheme.Tate.Full GD T) :
    TateTwist.Divisibility.restrictAway Γ(T.left, ⊤) p
        (integralWeilValue preservation composition unitCoherence associativity
          comparison symmetry stability hA MA evaluationA compatibility T (fun _ => True) x y) =
      (awayPair p) (GroupScheme.Tate.restrictAway A.toGrp T p x)
        (GroupScheme.Tate.restrictAway GD T p y) :=
  rfl

/-- Uniqueness follows from equality in every actual torsion coordinate. -/
lemma integralWeilValue_unique
    (q : GroupScheme.Tate.Integral A.toGrp T P →
      GroupScheme.Tate.Integral GD T P →
        TateTwist.Divisibility.Integral Γ(T.left, ⊤) P)
    (hq : ∀ n x y, TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n (q x y) =
      levelPair n.val T (x.val n) (y.val n)) :
    q = limitPair := by
  funext x y
  apply Subtype.ext
  funext n
  exact hq n x y

/-- Joint continuity uses discrete levels and the existing inverse-limit topologies. -/
lemma continuous_integralWeilValue :
    Continuous (fun z : GroupScheme.Tate.Integral A.toGrp T P ×
      GroupScheme.Tate.Integral GD T P => limitPair z.1 z.2) := by
  have hc : Continuous (fun z : GroupScheme.Tate.Integral A.toGrp T P ×
      GroupScheme.Tate.Integral GD T P => fun n : GroupScheme.Tate.Index P =>
        levelPair n.val T (z.1.val n) (z.2.val n)) :=
    continuous_pi (fun n =>
      continuous_tateLevelEvaluationPair A.toGrp GD T P n
        (fun x y => levelPair n.val T x y))
  exact hc.subtype_mk _

end Langlands.AbelianScheme
