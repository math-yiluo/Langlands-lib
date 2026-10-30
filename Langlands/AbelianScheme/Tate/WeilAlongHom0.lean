import Langlands.AbelianScheme.Tate.WeilRationalAlongHom
import Langlands.AbelianScheme.Rational

/-! # Weil pairings along actual rational dual-valued homomorphisms -/

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
local notation "rationalPairing" => rationalWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Pull back the constructed rational Weil pairing along an actual rational
homomorphism to the constructed dual, in the second variable. -/
def rationalWeilAlongHom0BilinearMap (lam : Hom0 A DA) (P : ℕ → Prop) :
    Tate.Rational A T P →ₗ[ℚ] Tate.Rational A T P →ₗ[ℚ]
      TateTwist.Divisibility.Rational Γ(T.left, ⊤) P :=
  (rationalPairing P).compl₂ (Tate.rationalHomMap T P lam)

local notation "along0" => rationalWeilAlongHom0BilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T

@[simp]
lemma rationalWeilAlongHom0BilinearMap_apply (lam : Hom0 A DA) (P : ℕ → Prop)
    (x y : Tate.Rational A T P) :
    along0 lam P x y = rationalPairing P x (Tate.rationalHomMap T P lam y) := rfl

/-- Including an integral dual-valued map recovers the published pullback pairing. -/
@[simp]
lemma rationalWeilAlongHom0BilinearMap_ofHom (lam : A ⟶ DA) (P : ℕ → Prop) :
    along0 (Rationalization.ofHom lam) P =
      rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change rationalPairing P x (Tate.rationalHomMap T P (Rationalization.ofHom lam) y) = _
  rw [Tate.rationalHomMap_ofHom]
  rfl

/-- The rational dual-valued homomorphism enters linearly. -/
lemma rationalWeilAlongHom0BilinearMap_add (lam mu : Hom0 A DA) (P : ℕ → Prop)
    (x y : Tate.Rational A T P) :
    along0 (lam + mu) P x y = along0 lam P x y + along0 mu P x y := by
  simp only [rationalWeilAlongHom0BilinearMap_apply, map_add, LinearMap.add_apply]

lemma rationalWeilAlongHom0BilinearMap_smul (q : ℚ) (lam : Hom0 A DA) (P : ℕ → Prop)
    (x y : Tate.Rational A T P) :
    along0 (q • lam) P x y = q • along0 lam P x y := by
  simp only [rationalWeilAlongHom0BilinearMap_apply, map_smul, LinearMap.smul_apply]

/-- The same pullback bundled over the existing finite adele ring. -/
def adelicWeilAlongHom0BilinearMap (lam : Hom0 A DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
    let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
    Tate.Rational A T P →ₗ[Global.FiniteAdeles ℚ]
      Tate.Rational A T P →ₗ[Global.FiniteAdeles ℚ]
        TateTwist.Divisibility.Rational Γ(T.left, ⊤) P := by
  let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
  let := GroupScheme.Tate.finiteAdeleModule (DA).toGrp T P h
  let := GroupScheme.Tate.finiteAdeleModule GD T P h
  let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
  exact (adelicWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T P h).compl₂
      (Tate.finiteAdeleHomMap T P h lam)

@[simp]
lemma adelicWeilAlongHom0BilinearMap_apply (lam : Hom0 A DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (x y : Tate.Rational A T P) :
    adelicWeilAlongHom0BilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P h x y =
        along0 lam P x y := rfl

/-- Integral maps recover the existing finite-adelic pullback bundle. -/
@[simp]
lemma adelicWeilAlongHom0BilinearMap_ofHom (lam : A ⟶ DA) (P : ℕ → Prop)
    (h : Global.RationalProfiniteIntegerAdeleComparison) :
    adelicWeilAlongHom0BilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T
      (Rationalization.ofHom lam) P h =
    adelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P h := rfl

/-- Pullback along the actual rational map over the prime-to-modulus adele ring. -/
def awayAdelicWeilAlongHom0BilinearMap (lam : Hom0 A DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
    Tate.RationalAway A T m →ₗ[Global.PrimeToFiniteAdeles m]
      Tate.RationalAway A T m →ₗ[Global.PrimeToFiniteAdeles m]
        TateTwist.Divisibility.RationalAway Γ(T.left, ⊤) m := by
  let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule (DA).toGrp T hAway
  let := GroupScheme.Tate.primeToFiniteAdeleModule GD T hAway
  let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
  exact (awayAdelicWeilBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA MA evaluationA compatibility T hAway).compl₂
      (Tate.primeToFiniteAdeleHomMap T hAway lam)

@[simp]
lemma awayAdelicWeilAlongHom0BilinearMap_apply (lam : Hom0 A DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
    (x y : Tate.RationalAway A T m) :
    awayAdelicWeilAlongHom0BilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam hAway x y =
        along0 lam (fun n => Nat.Coprime n m) x y := rfl

@[simp]
lemma awayAdelicWeilAlongHom0BilinearMap_ofHom (lam : A ⟶ DA)
    {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) :
    awayAdelicWeilAlongHom0BilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T
      (Rationalization.ofHom lam) hAway =
    awayAdelicWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam hAway := rfl

end Langlands.AbelianScheme
