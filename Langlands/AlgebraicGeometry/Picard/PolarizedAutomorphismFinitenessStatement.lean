import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphisms
import Mathlib.GroupTheory.OrderOfElement

/-! # Finiteness of the actual integral polarized automorphism group -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option autoImplicit false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Milne, Proposition 17.5(a), for actual integral polarized automorphisms. -/
def PolarizedAutomorphismFinitenessStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (square : MumfordBundlePicardZeroStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    (composition : PullbackTensorCompositionStatement.{u})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
    (symmetry : PullbackTensorSymmetryStatement.{u})
    (stability : PicardZeroPullbackStatement.{u})
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω))))
    (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
    (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
      structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
    (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
      stability composition unitCoherence associativity comparison symmetry),
    IsPolarization preservation square universality A hA geometryA MA evaluationA stability
      composition unitCoherence associativity comparison symmetry lam →
    Finite (polarizedAutGroup preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA lam)

variable (finiteness : PolarizedAutomorphismFinitenessStatement.{u})
  (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of Ω))))
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "AutLam" => polarizedAutGroup preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA

variable (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry)
  (hlam : IsPolarization preservation square universality A hA geometryA MA evaluationA
    stability composition unitCoherence associativity comparison symmetry lam)

include finiteness square universality lam hlam

/-- Every actual integral polarized automorphism has finite order, from the finiteness target. -/
theorem polarizedAut_isOfFinOrder (f : AutLam lam) : IsOfFinOrder f := by
  have := finiteness preservation square universality composition unitCoherence associativity
    comparison symmetry stability Ω A hA geometryA MA evaluationA lam hlam
  exact isOfFinOrder_of_finite f

/-- A positive power is the identity both integrally and on the corresponding rational
self-isogeny. The same exponent works in both actual categories. -/
theorem polarizedAut_exists_pow_eq_one (f : AutLam lam) :
    ∃ n : ℕ, 0 < n ∧ f ^ n = 1 ∧
      (polarizedAutRationalization preservation composition unitCoherence associativity
        comparison symmetry stability hA geometryA MA evaluationA lam f) ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ := (polarizedAut_isOfFinOrder finiteness preservation square universality
    composition unitCoherence associativity comparison symmetry stability Ω A hA geometryA
    MA evaluationA lam hlam f).exists_pow_eq_one
  refine ⟨n, hn, hpow, ?_⟩
  rw [← map_pow, hpow, map_one]

end Langlands.AbelianScheme
