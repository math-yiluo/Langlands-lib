import Langlands.AbelianScheme.Tate.WeilPolarizationAlternationStatement

/-! # From the actual finite diagonal identity to integral alternation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

section Consequences

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (alternation : RelativeFiniteWeilAlternationStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "finiteAlong" => finiteWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA

include alternation

/-- The finite scheme-diagonal identity is valid on every test-scheme point. -/
lemma finiteWeilAlongPolarization_self (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (n : ℕ) (hn : 0 < n) (T : Over S)
    (x : Additive (T ⟶ (kernelCommGroupScheme (multiplication A (n : ℤ))).X)) :
    finiteAlong lam n T x x = 0 := by
  have hc := congrArg (fun q => x.toMul ≫ q)
    (alternation preservation square universality composition unitCoherence associativity
      comparison symmetry stability S A hA geometryA MA evaluationA lam hLam n hn)
  rw [← Category.assoc, prod.comp_lift, Category.comp_id, MonObj.comp_one] at hc
  apply Additive.toMul.injective
  rw [finiteWeilAlongHomBilinearMap_apply]
  exact hc

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u}) (T : Over S)

/-- Every positive selected coordinate has trivial polarization diagonal. -/
lemma integralWeilAlongPolarization_isAlt (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (P : ℕ → Prop) :
    (integralWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P).IsAlt := by
  intro x
  apply Subtype.ext
  funext n
  change TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n
    (integralWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P x x) = 0
  rw [evaluation_integralWeilAlongHomBilinearMap,
    finiteWeilAlongPolarization_self preservation square universality composition
      unitCoherence associativity comparison symmetry stability alternation hA geometryA
      MA evaluationA lam hLam n.val n.property.1 T, map_zero]

/-- The away scalar bundle has the same diagonal as the selected integral bundle. -/
lemma awayWeilAlongPolarization_isAlt (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (m : ℕ) :
    (awayWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam m).IsAlt :=
  integralWeilAlongPolarization_isAlt preservation square universality composition
    unitCoherence associativity comparison symmetry stability alternation hA geometryA
    MA evaluationA compatibility T lam hLam (fun n => Nat.Coprime n m)

/-- All prime-power coordinates have positive order and hence trivial diagonal. -/
lemma primeWeilAlongPolarization_isAlt (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (p : ℕ) [Fact p.Prime] :
    (primeWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T p lam).IsAlt := by
  intro x
  apply Subtype.ext
  funext n
  change TateTwist.evaluation Γ(T.left, ⊤) p n
    (primeWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T p lam x x) = 0
  rw [evaluation_primeWeilAlongHomBilinearMap,
    finiteWeilAlongPolarization_self preservation square universality composition
      unitCoherence associativity comparison symmetry stability alternation hA geometryA
      MA evaluationA lam hLam (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) T, map_zero]

end Consequences

/-- The selected, away and prime-adic consequences of relative finite alternation. -/
theorem integralPolarizationWeilAlternation :
    IntegralPolarizationWeilAlternationStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity comparison
    symmetry stability compatibility alternation S _ A hA geometryA MA evaluationA lam hLam T
  exact ⟨integralWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability alternation hA geometryA
      MA evaluationA compatibility T lam hLam,
    awayWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability alternation hA geometryA
      MA evaluationA compatibility T lam hLam,
    primeWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability alternation hA geometryA
      MA evaluationA compatibility T lam hLam⟩

end Langlands.AbelianScheme
