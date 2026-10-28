import Langlands.AbelianScheme.Tate.WeilAlongHom
import Langlands.AbelianScheme.Tate.WeilRational

/-! # Rational and adelic Weil pairings along actual dual-valued homomorphisms -/

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{u}) (T : Over S)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp
  (dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA stability
    composition unitCoherence associativity comparison symmetry)
local notation "integralAlong" => integralWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T
local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Pull back the actual rational Weil pairing by the rationalized Tate map. -/
def rationalWeilAlongHomBilinearMap (lam : A ⟶ DA) (P : ℕ → Prop) :
    GroupScheme.Tate.Rational A.toGrp T P →ₗ[ℚ]
      GroupScheme.Tate.Rational A.toGrp T P →ₗ[ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P :=
  (rationalPairing P).compl₂ (GroupScheme.Tate.rationalMap T P (groupHom lam))

local notation "rationalAlong" => rationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T

/-- The pullback is in the second variable, with no change of twist or normalization. -/
@[simp]
lemma rationalWeilAlongHomBilinearMap_apply (lam : A ⟶ DA) (P : ℕ → Prop)
    (x y : GroupScheme.Tate.Rational A.toGrp T P) :
    rationalAlong lam P x y =
      rationalPairing P x (GroupScheme.Tate.rationalMap T P (groupHom lam) y) := rfl

/-- Rationalizing the actual integral pullback multiplies the two rational factors. -/
@[simp]
lemma rationalWeilAlongHomBilinearMap_tmul (lam : A ⟶ DA) (P : ℕ → Prop)
    (q r : ℚ) (x y : GroupScheme.Tate.Integral A.toGrp T P) :
    rationalAlong lam P (q ⊗ₜ[ℤ] x) (r ⊗ₜ[ℤ] y) =
      (q * r) ⊗ₜ[ℤ] integralAlong lam P x y := by
  rw [rationalWeilAlongHomBilinearMap_apply, GroupScheme.Tate.rationalMap_tmul,
    rationalWeilBilinearMap_tmul]
  rfl

/-- The canonical rationalization maps preserve the actual integral pullback pairing. -/
@[simp]
lemma rationalWeilAlongHomBilinearMap_toRational (lam : A ⟶ DA) (P : ℕ → Prop)
    (x y : GroupScheme.Tate.Integral A.toGrp T P) :
    rationalAlong lam P (GroupScheme.Tate.toRational A.toGrp T P x)
        (GroupScheme.Tate.toRational A.toGrp T P y) =
      TateTwist.Divisibility.toRational Γ(T.left, ⊤) P (integralAlong lam P x y) := by
  change rationalAlong lam P ((1 : ℚ) ⊗ₜ[ℤ] x) ((1 : ℚ) ⊗ₜ[ℤ] y) =
    (1 : ℚ) ⊗ₜ[ℤ] integralAlong lam P x y
  rw [rationalWeilAlongHomBilinearMap_tmul, one_mul]

/-- Restriction to away orders commutes with the rational pullback pairing. -/
lemma rationalRestrictAway_rationalWeilAlongHomBilinearMap (lam : A ⟶ DA) (m : ℕ)
    (x y : GroupScheme.Tate.RationalFull A.toGrp T) :
    TateTwist.Divisibility.rationalRestrictAway Γ(T.left, ⊤) m
        (rationalAlong lam (fun _ => True) x y) =
      rationalAlong lam (fun n => Nat.Coprime n m)
        (GroupScheme.Tate.rationalRestrictAway A.toGrp T m x)
        (GroupScheme.Tate.rationalRestrictAway A.toGrp T m y) := by
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | tmul r y =>
      simp only [rationalWeilAlongHomBilinearMap_tmul,
        TateTwist.Divisibility.rationalRestrictAway_tmul,
        GroupScheme.Tate.rationalRestrictAway_tmul]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

include compatibility

/-- The actual rational pullback pairing, bundled over the existing finite adele ring. -/
def adelicWeilAlongHomBilinearMap (lam : A ⟶ DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
    let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
    GroupScheme.Tate.Rational A.toGrp T P →ₗ[Global.FiniteAdeles ℚ]
      GroupScheme.Tate.Rational A.toGrp T P →ₗ[Global.FiniteAdeles ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P := by
  let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
  let := GroupScheme.Tate.finiteAdeleModule (DA).toGrp T P h
  let := GroupScheme.Tate.finiteAdeleModule GD T P h
  let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
  exact (adelicWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T P h).compl₂
      (Tate.finiteAdeleHomMap T P h (Rationalization.ofHom lam))

/-- The adelic bundle has exactly the rational pullback value. -/
@[simp]
lemma adelicWeilAlongHomBilinearMap_apply (lam : A ⟶ DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (x y : GroupScheme.Tate.Rational A.toGrp T P) :
    adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P h x y =
        rationalAlong lam P x y := by
  change rationalPairing P x (Tate.rationalHomMap T P (Rationalization.ofHom lam) y) = _
  rw [Tate.rationalHomMap_ofHom]
  rfl

/-- The away rational pullback bundled over the existing prime-to-modulus adele ring. -/
def awayAdelicWeilAlongHomBilinearMap (lam : A ⟶ DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
    GroupScheme.Tate.RationalAway A.toGrp T m →ₗ[Global.PrimeToFiniteAdeles m]
      GroupScheme.Tate.RationalAway A.toGrp T m →ₗ[Global.PrimeToFiniteAdeles m]
        TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m := by
  let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule (DA).toGrp T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule GD T hAway
  let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
  exact (awayAdelicWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T hAway).compl₂
      (Tate.primeToFiniteAdeleHomMap T hAway (Rationalization.ofHom lam))

/-- The away adelic bundle also retains exactly the selected rational pullback value. -/
@[simp]
lemma awayAdelicWeilAlongHomBilinearMap_apply (lam : A ⟶ DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x y : GroupScheme.Tate.RationalAway A.toGrp T m) :
    awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam hAway x y =
        rationalAlong lam (fun n => Nat.Coprime n m) x y := by
  change rationalPairing (fun n => Nat.Coprime n m) x
    (Tate.rationalHomMap T (fun n => Nat.Coprime n m) (Rationalization.ofHom lam) y) = _
  rw [Tate.rationalHomMap_ofHom]
  rfl

end Langlands.AbelianScheme
