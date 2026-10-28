import Langlands.AbelianScheme.Tate.WeilRationalPrime
import Langlands.AbelianScheme.Tate.WeilRationalAlongHom

/-! # Rational prime-adic Weil pairings along actual homomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (T : Over S) (p : ℕ) [Fact p.Prime]

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primePair" => primeRationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T p
local notation "primeIntegralAlong" => primeWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T p
local notation "rationalAlong" => rationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T

/-- Pull back the rational prime-adic pairing by the actual rationalized Tate map. -/
def primeRationalWeilAlongHomBilinearMap (lam : A ⟶ DA) :
    GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
      GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
        TateTwist.Rational Γ(T.left, ⊤) p :=
  (primePair).compl₂ (GroupScheme.Tate.PrimeAdic.rationalMap T p (groupHom lam))

local notation "primeAlong" => primeRationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T p

/-- Only the second input is pulled back; the actual roots-of-unity twist is retained. -/
@[simp]
lemma primeRationalWeilAlongHomBilinearMap_apply (lam : A ⟶ DA)
    (x y : GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p) :
    primeAlong lam x y =
      primePair x (GroupScheme.Tate.PrimeAdic.rationalMap T p (groupHom lam) y) := rfl

/-- The pure-tensor formula recovers the integral pullback and its normalization. -/
@[simp]
lemma primeRationalWeilAlongHomBilinearMap_tmul (lam : A ⟶ DA)
    (q r : ℚ_[p]) (x y : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p) :
    primeAlong lam (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) =
      (q * r) ⊗ₜ[ℤ_[p]] primeIntegralAlong lam x y := by
  rw [primeRationalWeilAlongHomBilinearMap_apply,
    GroupScheme.Tate.PrimeAdic.rationalMap_tmul, primeRationalWeilBilinearMap_tmul]
  rfl

/-- The canonical rationalization maps commute with this pullback pairing. -/
@[simp]
lemma primeRationalWeilAlongHomBilinearMap_toRational (lam : A ⟶ DA)
    (x y : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p) :
    primeAlong lam (GroupScheme.Tate.PrimeAdic.toRational A.toGrp T p x)
        (GroupScheme.Tate.PrimeAdic.toRational A.toGrp T p y) =
      TateTwist.toRational Γ(T.left, ⊤) p (primeIntegralAlong lam x y) := by
  change primeAlong lam ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)
      ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y) =
    (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] primeIntegralAlong lam x y
  rw [primeRationalWeilAlongHomBilinearMap_tmul, one_mul]

/-- The pure-tensor normalization determines the rational prime-adic pullback. -/
lemma primeRationalWeilAlongHomBilinearMap_unique (lam : A ⟶ DA)
    (b : GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
      GroupScheme.Tate.PrimeAdic.Rational A.toGrp T p →ₗ[ℚ_[p]]
        TateTwist.Rational Γ(T.left, ⊤) p)
    (hb : ∀ (q r : ℚ_[p]) x y,
      b (q ⊗ₜ[ℤ_[p]] x) (r ⊗ₜ[ℤ_[p]] y) =
        (q * r) ⊗ₜ[ℤ_[p]] primeIntegralAlong lam x y) :
    b = primeAlong lam := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  apply TensorProduct.AlgebraTensorModule.ext
  intro r y
  exact (hb q r x y).trans
    (primeRationalWeilAlongHomBilinearMap_tmul preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T p lam q r x y).symm

/-- Extraction of any selected rational system commutes with the actual pullback. -/
lemma rationalToPrime_rationalWeilAlongHomBilinearMap (lam : A ⟶ DA)
    (P : ℕ → Prop) (hP : ∀ n, P (p ^ n))
    (x y : GroupScheme.Tate.Rational A.toGrp T P) :
    TateTwist.Divisibility.rationalToPrime Γ(T.left, ⊤) P p hP
        (rationalAlong lam P x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.rationalToPrime A.toGrp T P p hP x)
        (GroupScheme.Tate.PrimeComparison.rationalToPrime A.toGrp T P p hP y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      simp only [rationalWeilAlongHomBilinearMap_tmul,
        TateTwist.Divisibility.rationalToPrime_tmul,
        GroupScheme.Tate.PrimeComparison.rationalToPrime_tmul,
        primeRationalWeilAlongHomBilinearMap_tmul,
        toPrime_integralWeilAlongHomBilinearMap, Rat.cast_mul]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Every prime component of the full rational pullback is the prime-adic pullback. -/
lemma rationalFullToPrime_rationalWeilAlongHomBilinearMap (lam : A ⟶ DA)
    (x y : GroupScheme.Tate.RationalFull A.toGrp T) :
    TateTwist.Divisibility.rationalFullToPrime Γ(T.left, ⊤) p
        (rationalAlong lam (fun _ => True) x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p x)
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p y) :=
  rationalToPrime_rationalWeilAlongHomBilinearMap preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    T p lam (fun _ => True) (fun _ => trivial) x y

/-- Away rational extraction gives the same pullback at every retained prime. -/
lemma rationalAwayToPrime_rationalWeilAlongHomBilinearMap (lam : A ⟶ DA)
    (m : ℕ) (h : Nat.Coprime p m) (x y : GroupScheme.Tate.RationalAway A.toGrp T m) :
    TateTwist.Divisibility.rationalAwayToPrime Γ(T.left, ⊤) p m h
        (rationalAlong lam (fun n => Nat.Coprime n m) x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m h x)
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m h y) :=
  rationalToPrime_rationalWeilAlongHomBilinearMap preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    T p lam (fun n => Nat.Coprime n m) (fun n => h.pow_left n) x y

/-- The full adelic bundle has these same prime-adic rational components. -/
lemma rationalFullToPrime_adelicWeilAlongHomBilinearMap (lam : A ⟶ DA)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x y : GroupScheme.Tate.RationalFull A.toGrp T) :
    TateTwist.Divisibility.rationalFullToPrime Γ(T.left, ⊤) p
        (adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility T
          lam (fun _ => True) h x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p x)
        (GroupScheme.Tate.PrimeComparison.rationalFullToPrime A.toGrp T p y) := by
  simpa only [adelicWeilAlongHomBilinearMap_apply] using
    rationalFullToPrime_rationalWeilAlongHomBilinearMap preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      T p lam x y

/-- The away adelic bundle has the same components at every retained prime. -/
lemma rationalAwayToPrime_awayAdelicWeilAlongHomBilinearMap (lam : A ⟶ DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (hp : Nat.Coprime p m) (x y : GroupScheme.Tate.RationalAway A.toGrp T m) :
    TateTwist.Divisibility.rationalAwayToPrime Γ(T.left, ⊤) p m hp
        (awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
          comparison symmetry stability hA geometryA MA evaluationA compatibility T
          lam hAway x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m hp x)
        (GroupScheme.Tate.PrimeComparison.rationalAwayToPrime A.toGrp T p m hp y) := by
  simpa only [awayAdelicWeilAlongHomBilinearMap_apply] using
    rationalAwayToPrime_rationalWeilAlongHomBilinearMap preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
      T p lam m hp x y

end Langlands.AbelianScheme
