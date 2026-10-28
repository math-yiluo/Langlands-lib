import Langlands.AbelianScheme.Tate.WeilPrime
import Langlands.AbelianScheme.Tate.WeilRational
import Langlands.AbelianScheme.Tate.RationalPrime
import Langlands.AbelianScheme.Tate.TwistRationalPrime

/-! # The rational prime-adic Weil pairing and rational extraction -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

private def primeBaseChangePair {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W) :
    (K ⊗[R] M) →ₗ[K] (K ⊗[R] N) →ₗ[K] (K ⊗[R] W) :=
  TensorProduct.curry (((TensorProduct.lift b).baseChange K).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K M N).symm.toLinearMap)

@[simp]
private lemma primeBaseChangePair_tmul {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W)
    (q r : K) (x : M) (y : N) :
    primeBaseChangePair K b (q ⊗ₜ[R] x) (r ⊗ₜ[R] y) = (q * r) ⊗ₜ[R] b x y := by
  simp [primeBaseChangePair, TensorProduct.curry_apply]

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
local notation "integralPrimePair" => primeWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T p
local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Extend the actual prime-adic Weil pairing and its roots twist from Z_p to Q_p. -/
def primeRationalWeilBilinearMap :
    GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
      GroupScheme.Tate.PrimeAdic.Rational GD T p →ₗ[ℚ_[p]]
        TateTwist.Rational Γ(T.left, ⊤) p :=
  primeBaseChangePair ℚ_[p] integralPrimePair

local notation "primeRationalPair" => primeRationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T p

/-- The pure-tensor formula preserves the integral Weil normalization. -/
@[simp]
lemma primeRationalWeilBilinearMap_tmul (q r : ℚ_[p])
    (x : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p)
    (y : GroupScheme.Tate.PrimeAdic.Integral GD T p) :
    primeRationalPair (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) =
      (q * r) ⊗ₜ[ℤ_[p]] integralPrimePair x y :=
  primeBaseChangePair_tmul ℚ_[p] _ q r x y

/-- The canonical rationalization maps commute with the integral pairing. -/
@[simp]
lemma primeRationalWeilBilinearMap_toRational
    (x : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p)
    (y : GroupScheme.Tate.PrimeAdic.Integral GD T p) :
    primeRationalPair (GroupScheme.Tate.PrimeAdic.toRational A.toGrp T p x)
        (GroupScheme.Tate.PrimeAdic.toRational GD T p y) =
      TateTwist.toRational Γ(T.left, ⊤) p (integralPrimePair x y) := by
  change primeRationalPair ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x) ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) =
    (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] integralPrimePair x y
  simpa only [one_mul] using
    primeRationalWeilBilinearMap_tmul preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA compatibility T p 1 1 x y

/-- Values on pure tensors determine the Q_p-bilinear extension uniquely. -/
lemma primeRationalWeilBilinearMap_unique
    (b : GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
      GroupScheme.Tate.PrimeAdic.Rational GD T p →ₗ[ℚ_[p]]
        TateTwist.Rational Γ(T.left, ⊤) p)
    (hb : ∀ (q r : ℚ_[p]) x y,
      b (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) =
        (q * r) ⊗ₜ[ℤ_[p]] integralPrimePair x y) :
    b = primeRationalPair := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  apply TensorProduct.AlgebraTensorModule.ext
  intro r y
  exact (hb q r x y).trans
    (primeRationalWeilBilinearMap_tmul preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA compatibility T p q r x y).symm

/-- Rational extraction of any selected system commutes with the Weil pairing. -/
lemma rationalToPrime_rationalWeilBilinearMap (P : ℕ → Prop) (hP : ∀ n, P (p ^ n))
    (x : GroupScheme.Tate.Rational A.toGrp T P)
    (y : GroupScheme.Tate.Rational GD T P) :
    TateTwist.Divisibility.rationalToPrime Γ(T.left, ⊤) P p hP
        (rationalPairing P x y) =
      primeRationalPair
        (GroupScheme.Tate.PrimeComparison.rationalToPrime A.toGrp T P p hP x)
        (GroupScheme.Tate.PrimeComparison.rationalToPrime GD T P p hP y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      simp only [rationalWeilBilinearMap_tmul,
        TateTwist.Divisibility.rationalToPrime_tmul,
        GroupScheme.Tate.PrimeComparison.rationalToPrime_tmul,
        primeRationalWeilBilinearMap_tmul, integralWeilBilinearMap_apply,
        primeWeilBilinearMap_apply, toPrime_integralWeilValue, Rat.cast_mul]
    | add y z hy hz => simp_all
  | add x z hx hz => simp_all

/-- Each rational prime component of the full pairing is the Q_p pairing. -/
lemma rationalFullToPrime_rationalWeilBilinearMap
    (x : GroupScheme.Tate.RationalFull A.toGrp T)
    (y : GroupScheme.Tate.RationalFull GD T) :
    TateTwist.Divisibility.rationalFullToPrime Γ(T.left, ⊤) p
        (rationalPairing (fun _ => True) x y) =
      primeRationalPair
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p x)
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime GD T p y) :=
  rationalToPrime_rationalWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T p
    (fun _ => True) (fun _ => trivial) x y

/-- The same formula holds at each prime retained by the away system. -/
lemma rationalAwayToPrime_rationalWeilBilinearMap (m : ℕ) (h : Nat.Coprime p m)
    (x : GroupScheme.Tate.RationalAway A.toGrp T m)
    (y : GroupScheme.Tate.RationalAway GD T m) :
    TateTwist.Divisibility.rationalAwayToPrime Γ(T.left, ⊤) p m h
        (rationalPairing (fun n => Nat.Coprime n m) x y) =
      primeRationalPair
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m h x)
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime GD T p m h y) :=
  rationalToPrime_rationalWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T p
    (fun n => Nat.Coprime n m) (fun n => h.pow_left n) x y

end Langlands.AbelianScheme
