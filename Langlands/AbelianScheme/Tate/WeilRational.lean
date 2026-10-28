import Langlands.AbelianScheme.Tate.WeilIntegral
import Langlands.AbelianScheme.Tate.TwistAwayRationalScalars
import Mathlib.LinearAlgebra.BilinearMap

/-! # Rational and finite-adelic Weil pairings with the actual Tate twist -/

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

private def baseChangePair {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W) :
    (K ⊗[R] M) →ₗ[K] (K ⊗[R] N) →ₗ[K] (K ⊗[R] W) :=
  TensorProduct.curry (((TensorProduct.lift b).baseChange K).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange R K M N).symm.toLinearMap)

@[simp]
private lemma baseChangePair_tmul {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W)
    (q r : K) (x : M) (y : N) :
    baseChangePair K b (q ⊗ₜ[R] x) (r ⊗ₜ[R] y) = (q * r) ⊗ₜ[R] b x y := by
  simp [baseChangePair, TensorProduct.curry_apply]

private def rationalPair {R : Type*} [CommRing R]
    {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W) :
    (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℚ ⊗[ℤ] N) →ₗ[ℚ] (ℚ ⊗[ℤ] W) :=
  baseChangePair ℚ (b.restrictScalars₁₂ ℤ ℤ)

@[simp]
private lemma rationalPair_tmul {R : Type*} [CommRing R]
    {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W)
    (q r : ℚ) (x : M) (y : N) :
    rationalPair b (q ⊗ₜ[ℤ] x) (r ⊗ₜ[ℤ] y) = (q * r) ⊗ₜ[ℤ] b x y :=
  baseChangePair_tmul ℚ _ q r x y

private lemma rationalPair_action_left {R : Type*} [CommRing R]
    {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W)
    (a : ℚ ⊗[ℤ] R) (x : ℚ ⊗[ℤ] M) (y : ℚ ⊗[ℤ] N) :
    rationalPair b (TateScalarExtension.action R M a x) y =
      TateScalarExtension.action R W a (rationalPair b x y) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y => simp [TateScalarExtension.action_tmul, mul_assoc]
      | add y z hy hz => simp_all
    | add x z hx hz => simp_all
  | add a c ha hc => simp_all

private lemma rationalPair_action_right {R : Type*} [CommRing R]
    {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module R M] [Module R N] [Module R W] (b : M →ₗ[R] N →ₗ[R] W)
    (a : ℚ ⊗[ℤ] R) (x : ℚ ⊗[ℤ] M) (y : ℚ ⊗[ℤ] N) :
    rationalPair b x (TateScalarExtension.action R N a y) =
      TateScalarExtension.action R W a (rationalPair b x y) := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y => simp [TateScalarExtension.action_tmul, mul_left_comm]
      | add y z hy hz => simp_all
    | add x z hx hz => simp_all
  | add a c ha hc => simp_all

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
  (T : Over S)

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp GA
local notation "integralPair" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Rational extension of the intrinsic pairing on any selected divisibility system. -/
def rationalWeilBilinearMap (P : ℕ → Prop) :
    GroupScheme.Tate.Rational A.toGrp T P →ₗ[ℚ]
      GroupScheme.Tate.Rational GD T P →ₗ[ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P :=
  rationalPair (integralPair P)

local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Rational scalar factors multiply, and the finite Weil normalization is retained. -/
@[simp]
lemma rationalWeilBilinearMap_tmul (P : ℕ → Prop) (q r : ℚ)
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    rationalPairing P (q ⊗ₜ[ℤ] x) (r ⊗ₜ[ℤ] y) =
      (q * r) ⊗ₜ[ℤ] integralPair P x y :=
  rationalPair_tmul _ q r x y

/-- The rational pairing extends the integral pairing through the canonical maps. -/
@[simp]
lemma rationalWeilBilinearMap_toRational (P : ℕ → Prop)
    (x : GroupScheme.Tate.Integral A.toGrp T P)
    (y : GroupScheme.Tate.Integral GD T P) :
    rationalPairing P (GroupScheme.Tate.toRational A.toGrp T P x)
        (GroupScheme.Tate.toRational GD T P y) =
      TateTwist.Divisibility.toRational Γ(T.left, ⊤) P (integralPair P x y) := by
  change rationalPairing P ((1 : ℚ) ⊗ₜ[ℤ] x) ((1 : ℚ) ⊗ₜ[ℤ] y) =
    (1 : ℚ) ⊗ₜ[ℤ] integralPair P x y
  simpa only [one_mul] using
    rationalWeilBilinearMap_tmul preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T P 1 1 x y

/-- Values on pure tensors uniquely determine the rational bilinear pairing. -/
lemma rationalWeilBilinearMap_unique (P : ℕ → Prop)
    (b : GroupScheme.Tate.Rational A.toGrp T P →ₗ[ℚ]
      GroupScheme.Tate.Rational GD T P →ₗ[ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P)
    (hb : ∀ (q r : ℚ) x y,
      b (q ⊗ₜ[ℤ] x) (r ⊗ₜ[ℤ] y) = (q * r) ⊗ₜ[ℤ] integralPair P x y) :
    b = rationalPairing P := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  apply TensorProduct.AlgebraTensorModule.ext
  intro r y
  rw [hb, rationalWeilBilinearMap_tmul]

/-- Restriction to prime-to-modulus orders commutes with rational Weil pairing. -/
lemma rationalRestrictAway_rationalWeilBilinearMap (m : ℕ)
    (x : GroupScheme.Tate.RationalFull A.toGrp T)
    (y : GroupScheme.Tate.RationalFull GD T) :
    TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m
        (rationalPairing (fun _ => True) x y) =
      rationalPairing (fun n => Nat.Coprime n m)
        (GroupScheme.Tate.rationalRestrictAway A.toGrp T m x)
        (GroupScheme.Tate.rationalRestrictAway GD T m y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      simp only [rationalWeilBilinearMap_tmul,
        TateTwist.Divisibility.rationalRestrictAway_tmul,
        GroupScheme.Tate.rationalRestrictAway_tmul]
      rfl
    | add y z hy hz => simp_all
  | add x z hx hz => simp_all

/-- The same scalar comparison on inputs and twist gives left adelic linearity. -/
lemma rationalWeilBilinearMap_finiteAdeleAction_left (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (a : Global.FiniteAdeles ℚ)
    (x : GroupScheme.Tate.Rational A.toGrp T P)
    (y : GroupScheme.Tate.Rational GD T P) :
    rationalPairing P (GroupScheme.Tate.finiteAdeleAction A.toGrp T P h a x) y =
      TateTwist.Divisibility.finiteAdeleAction Γ(T.left, ⊤) P h a
        (rationalPairing P x y) :=
  rationalPair_action_left (integralPair P) _ x y

/-- The same scalar comparison also gives right adelic linearity. -/
lemma rationalWeilBilinearMap_finiteAdeleAction_right (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (a : Global.FiniteAdeles ℚ)
    (x : GroupScheme.Tate.Rational A.toGrp T P)
    (y : GroupScheme.Tate.Rational GD T P) :
    rationalPairing P x (GroupScheme.Tate.finiteAdeleAction GD T P h a y) =
      TateTwist.Divisibility.finiteAdeleAction Γ(T.left, ⊤) P h a
        (rationalPairing P x y) :=
  rationalPair_action_right (integralPair P) _ x y

/-- The actual rational Weil pairing, bundled over the existing finite adele ring. -/
def adelicWeilBilinearMap (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
    let := GroupScheme.Tate.finiteAdeleModule GD T P h
    let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
    GroupScheme.Tate.Rational A.toGrp T P →ₗ[Global.FiniteAdeles ℚ]
      GroupScheme.Tate.Rational GD T P →ₗ[Global.FiniteAdeles ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P := by
  let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
  let := GroupScheme.Tate.finiteAdeleModule GD T P h
  let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
  exact
    { toFun x :=
        { (rationalPairing P x).toAddHom with
          map_smul' := fun a y =>
            rationalWeilBilinearMap_finiteAdeleAction_right preservation composition
              unitCoherence associativity comparison symmetry stability hA MA evaluationA
              compatibility T P h a x y }
      map_add' x x' := LinearMap.ext fun y =>
        DFunLike.congr_fun (map_add (rationalPairing P) x x') y
      map_smul' a x := LinearMap.ext fun y =>
        rationalWeilBilinearMap_finiteAdeleAction_left preservation composition
          unitCoherence associativity comparison symmetry stability hA MA evaluationA
          compatibility T P h a x y }

@[simp]
lemma adelicWeilBilinearMap_apply (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x : GroupScheme.Tate.Rational A.toGrp T P)
    (y : GroupScheme.Tate.Rational GD T P) :
    adelicWeilBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T P h x y = rationalPairing P x y := rfl

/-- The coupled away comparison gives left prime-to-modulus adelic linearity. -/
lemma rationalWeilBilinearMap_primeToFiniteAdeleAction_left
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (a : Global.PrimeToFiniteAdeles m)
    (x : GroupScheme.Tate.RationalAway A.toGrp T m)
    (y : GroupScheme.Tate.RationalAway GD T m) :
    rationalPairing (fun n => Nat.Coprime n m)
        (GroupScheme.Tate.primeToFiniteAdeleAction A.toGrp T hAway a x) y =
      TateTwist.Divisibility.primeToFiniteAdeleAction Γ(T.left, ⊤) hAway a
        (rationalPairing (fun n => Nat.Coprime n m) x y) :=
  rationalPair_action_left
    (awayWeilBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T m) _ x y

/-- The coupled away comparison also gives right adelic linearity. -/
lemma rationalWeilBilinearMap_primeToFiniteAdeleAction_right
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (a : Global.PrimeToFiniteAdeles m)
    (x : GroupScheme.Tate.RationalAway A.toGrp T m)
    (y : GroupScheme.Tate.RationalAway GD T m) :
    rationalPairing (fun n => Nat.Coprime n m) x
        (GroupScheme.Tate.primeToFiniteAdeleAction GD T hAway a y) =
      TateTwist.Divisibility.primeToFiniteAdeleAction Γ(T.left, ⊤) hAway a
        (rationalPairing (fun n => Nat.Coprime n m) x y) :=
  rationalPair_action_right
    (awayWeilBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T m) _ x y

/-- The same rational pairing bundled over the existing prime-to-modulus adele ring. -/
def awayAdelicWeilBilinearMap
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
    let := GroupScheme.Tate.primeToFiniteAdeleModule GD T hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
    GroupScheme.Tate.RationalAway A.toGrp T m →ₗ[Global.PrimeToFiniteAdeles m]
      GroupScheme.Tate.RationalAway GD T m →ₗ[Global.PrimeToFiniteAdeles m]
        TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m := by
  let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule GD T hAway
  let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
  exact
    { toFun x :=
        { (rationalPairing (fun n => Nat.Coprime n m) x).toAddHom with
          map_smul' := fun a y =>
            rationalWeilBilinearMap_primeToFiniteAdeleAction_right preservation composition
              unitCoherence associativity comparison symmetry stability hA MA evaluationA
              compatibility T hAway a x y }
      map_add' x x' := LinearMap.ext fun y =>
        DFunLike.congr_fun (map_add (rationalPairing (fun n => Nat.Coprime n m)) x x') y
      map_smul' a x := LinearMap.ext fun y =>
        rationalWeilBilinearMap_primeToFiniteAdeleAction_left preservation composition
          unitCoherence associativity comparison symmetry stability hA MA evaluationA
          compatibility T hAway a x y }

@[simp]
lemma awayAdelicWeilBilinearMap_apply
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x : GroupScheme.Tate.RationalAway A.toGrp T m)
    (y : GroupScheme.Tate.RationalAway GD T m) :
    awayAdelicWeilBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA MA evaluationA compatibility T hAway x y =
        rationalPairing (fun n => Nat.Coprime n m) x y := rfl

end Langlands.AbelianScheme
