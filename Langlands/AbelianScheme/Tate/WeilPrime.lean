import Langlands.AbelianScheme.Tate.WeilIntegral
import Langlands.AbelianScheme.Tate.PrimeComparison

/-! # The actual prime-adic Weil pairing, conditional on relative compatibility -/

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

private lemma continuous_primeLevelEvaluationPair {S : Scheme.{u}}
    (G H : Grp (Over S)) [IsCommMonObj G.X] [IsCommMonObj H.X]
    (T : Over S) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {C : Type*} [TopologicalSpace C]
    (f : GroupScheme.Tate.Level G T (p ^ n) →
      GroupScheme.Tate.Level H T (p ^ n) → C) :
    Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral G T p ×
      GroupScheme.Tate.PrimeAdic.Integral H T p => f (z.1.val n) (z.2.val n)) :=
  (continuous_of_discreteTopology
    (f := fun z : GroupScheme.Tate.Level G T (p ^ n) ×
      GroupScheme.Tate.Level H T (p ^ n) => f z.1 z.2)).comp
        (((GroupScheme.Tate.PrimeAdic.continuous_evaluation G T p n).comp
          continuous_fst).prodMk
          ((GroupScheme.Tate.PrimeAdic.continuous_evaluation H T p n).comp
            continuous_snd))

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (T : Over S) (p : ℕ) [Fact p.Prime]

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp GA
local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA

/-- Pair the actual prime-power torsion coordinates into a coherent family of roots. -/
def primeWeilValue (x : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p)
    (y : GroupScheme.Tate.PrimeAdic.Integral GD T p) :
    TateTwist.Integral Γ(T.left, ⊤) p :=
  ⟨fun n => levelPair (p ^ n) T (x.val n) (y.val n), by
    intro n
    rw [finiteWeilLevelBilinearMap_transition preservation composition unitCoherence
      associativity comparison symmetry stability hA MA evaluationA compatibility T
      (pow_pos (Fact.out : p.Prime).pos n)
      (pow_pos (Fact.out : p.Prime).pos (n + 1))
      (pow_dvd_pow p (Nat.le_succ n)), x.property n, y.property n]⟩

local notation "primePair" => primeWeilValue preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T p

/-- The coordinate formula retains the original finite Weil normalization. -/
@[simp]
lemma evaluation_primeWeilValue (n : ℕ)
    (x : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p)
    (y : GroupScheme.Tate.PrimeAdic.Integral GD T p) :
    TateTwist.evaluation Γ(T.left, ⊤) p n (primePair x y) =
      levelPair (p ^ n) T (GroupScheme.Tate.PrimeAdic.evaluation A.toGrp T p n x)
        (GroupScheme.Tate.PrimeAdic.evaluation GD T p n y) := rfl

/-- The actual prime-adic Weil pairing is bilinear over the p-adic integers. -/
def primeWeilBilinearMap :
    GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p →ₗ[ℤ_[p]]
      GroupScheme.Tate.PrimeAdic.Integral GD T p →ₗ[ℤ_[p]]
        TateTwist.Integral Γ(T.left, ⊤) p where
  toFun x :=
    { toFun := primePair x
      map_add' y y' := by
        apply Subtype.ext
        funext n
        exact map_add (levelPair (p ^ n) T (x.val n)) (y.val n) (y'.val n)
      map_smul' a y := by
        apply Subtype.ext
        funext n
        exact ZMod.map_smul (levelPair (p ^ n) T (x.val n))
          (PadicInt.toZModPow n a) (y.val n) }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    exact DFunLike.congr_fun (map_add (levelPair (p ^ n) T) (x.val n) (x'.val n))
      (y.val n)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext n
    let f : GroupScheme.Tate.Level A.toGrp T (p ^ n) →+
        TateTwist.Level Γ(T.left, ⊤) (p ^ n) :=
      { toFun := fun z => levelPair (p ^ n) T z (y.val n)
        map_zero' := by rw [map_zero, AddMonoidHom.zero_apply]
        map_add' z z' := DFunLike.congr_fun
          (map_add (levelPair (p ^ n) T) z z') (y.val n) }
    exact ZMod.map_smul f (PadicInt.toZModPow n a) (x.val n)

@[simp]
lemma primeWeilBilinearMap_apply
    (x : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p)
    (y : GroupScheme.Tate.PrimeAdic.Integral GD T p) :
    primeWeilBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T p x y = primePair x y := rfl

/-- Equality in every prime-power coordinate determines the pairing uniquely. -/
lemma primeWeilValue_unique
    (q : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p →
      GroupScheme.Tate.PrimeAdic.Integral GD T p →
        TateTwist.Integral Γ(T.left, ⊤) p)
    (hq : ∀ n x y, TateTwist.evaluation Γ(T.left, ⊤) p n (q x y) =
      levelPair (p ^ n) T (x.val n) (y.val n)) :
    q = primePair := by
  funext x y
  apply Subtype.ext
  funext n
  exact hq n x y

/-- Joint continuity for the existing inverse-limit topologies. -/
lemma continuous_primeWeilValue :
    Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p ×
      GroupScheme.Tate.PrimeAdic.Integral GD T p => primePair z.1 z.2) := by
  have hc : Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p ×
      GroupScheme.Tate.PrimeAdic.Integral GD T p => fun n : ℕ =>
        levelPair (p ^ n) T (z.1.val n) (z.2.val n)) :=
    continuous_pi (fun n =>
      continuous_primeLevelEvaluationPair A.toGrp GD T p n
        (fun x y => levelPair (p ^ n) T x y))
  exact hc.subtype_mk _

/-- Extracting prime-power coordinates commutes with the selected Weil pairing. -/
lemma toPrime_integralWeilValue (P : ℕ → Prop) (hP : ∀ n, P (p ^ n))
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    TateTwist.Divisibility.toPrime Γ(T.left, ⊤) P p hP
        (integralWeilValue preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA compatibility T P x y) =
      primePair (GroupScheme.Tate.PrimeComparison.toPrime A.toGrp T P p hP x)
        (GroupScheme.Tate.PrimeComparison.toPrime GD T P p hP y) := rfl

/-- The full pairing has the constructed prime-adic pairing as each prime component. -/
lemma fullToPrime_integralWeilValue
    (x : GroupScheme.Tate.Full A.toGrp T) (y : GroupScheme.Tate.Full GD T) :
    TateTwist.Divisibility.fullToPrime Γ(T.left, ⊤) p
        (integralWeilValue preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA compatibility T (fun _ => True) x y) =
      primePair (GroupScheme.Tate.PrimeComparison.fullToPrime A.toGrp T p x)
        (GroupScheme.Tate.PrimeComparison.fullToPrime GD T p y) := rfl

/-- The same comparison holds at every prime retained by an away system. -/
lemma awayToPrime_integralWeilValue (m : ℕ) (h : Nat.Coprime p m)
    (x : GroupScheme.Tate.Away A.toGrp T m) (y : GroupScheme.Tate.Away GD T m) :
    TateTwist.Divisibility.awayToPrime Γ(T.left, ⊤) p m h
        (integralWeilValue preservation composition unitCoherence associativity comparison
          symmetry stability hA MA evaluationA compatibility T (fun n => Nat.Coprime n m) x y) =
      primePair (GroupScheme.Tate.PrimeComparison.awayToPrime A.toGrp T p m h x)
        (GroupScheme.Tate.PrimeComparison.awayToPrime GD T p m h y) := rfl

end Langlands.AbelianScheme
