import Langlands.AbelianScheme.Tate.WeilRationalPolarizationAlternationStatement
import Langlands.AbelianScheme.Tate.WeilPolarizationAlternationProof

/-! # Scalar extension preserves polarization Weil alternation -/

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

private lemma isAlt_of_pureTensorFormula {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] {M W : Type*} [AddCommGroup M] [AddCommGroup W]
    [Module R M] [Module R W] (b : M → M → W)
    (hAlt : ∀ x, b x x = 0) (hSkew : ∀ x y, -b x y = b y x)
    (B : (K ⊗[R] M) →ₗ[K] (K ⊗[R] M) →ₗ[K] (K ⊗[R] W))
    (hB : ∀ (q r : K) x y,
      B (q ⊗ₜ[R] x) (r ⊗ₜ[R] y) = (q * r) ⊗ₜ[R] b x y) :
    B.IsAlt := by
  have hBSkew : ∀ x y, -B x y = B y x := by
    intro x y
    induction x using TensorProduct.inductionOn with
    | tmul q x =>
      induction y using TensorProduct.inductionOn with
      | tmul r y => rw [hB, hB, ← TensorProduct.tmul_neg, hSkew, mul_comm]
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, neg_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, neg_add, hx, hz]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q x => rw [hB, hAlt, TensorProduct.tmul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    exact add_eq_zero_iff_neg_eq.mpr (hBSkew y x)

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (alternation : RelativeFiniteWeilAlternationStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (T : Over S)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

include alternation

/-- The rational selected pullback extends the actual alternating integral pairing. -/
lemma rationalWeilAlongPolarization_isAlt (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (P : ℕ → Prop) :
    (rationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P).IsAlt := by
  let b := integralWeilAlongHomBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility T lam P
  have hb : b.IsAlt := integralWeilAlongPolarization_isAlt preservation square universality
    composition unitCoherence associativity comparison symmetry stability alternation
    hA geometryA MA evaluationA compatibility T lam hLam P
  exact isAlt_of_pureTensorFormula (R := ℤ) (K := ℚ) (fun x y => b x y) hb hb.neg
    _ (rationalWeilAlongHomBilinearMap_tmul preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T lam P)

/-- The prime-adic rational pullback extends the alternating integral prime pairing. -/
lemma primeRationalWeilAlongPolarization_isAlt (lam : A ⟶ DA)
    (hLam : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (p : ℕ) [Fact p.Prime] :
    (primeRationalWeilAlongHomBilinearMap preservation composition unitCoherence associativity
      comparison symmetry stability hA geometryA MA evaluationA compatibility T p lam).IsAlt := by
  let b := primeWeilAlongHomBilinearMap preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA compatibility T p lam
  have hb : b.IsAlt := primeWeilAlongPolarization_isAlt preservation square universality
    composition unitCoherence associativity comparison symmetry stability alternation
    hA geometryA MA evaluationA compatibility T lam hLam p
  exact isAlt_of_pureTensorFormula (R := ℤ_[p]) (K := ℚ_[p]) (fun x y => b x y) hb hb.neg
    _ (primeRationalWeilAlongHomBilinearMap_tmul preservation composition unitCoherence
      associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T p lam)

end Consequences

/-- Relative finite alternation passes to the rational and adelic polarization pairings. -/
theorem rationalPolarizationWeilAlternation :
    RationalPolarizationWeilAlternationStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity comparison
    symmetry stability compatibility alternation S _ A hA geometryA MA evaluationA lam hLam T
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact rationalWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability compatibility alternation
      hA geometryA MA evaluationA T lam hLam
  · exact primeRationalWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability compatibility alternation
      hA geometryA MA evaluationA T lam hLam
  · intro P h
    let := GroupScheme.Tate.finiteAdeleModule A.toGrp T P h
    let := TateTwist.Divisibility.finiteAdeleModule Γ(T.left, ⊤) P h
    dsimp only [LinearMap.IsAlt]
    intro x
    rw [adelicWeilAlongHomBilinearMap_apply]
    exact rationalWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability compatibility alternation
      hA geometryA MA evaluationA T lam hLam P x
  · intro h m hAway
    let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp T hAway
    let := TateTwist.Divisibility.primeToFiniteAdeleModule Γ(T.left, ⊤) hAway
    dsimp only [LinearMap.IsAlt]
    intro x
    rw [awayAdelicWeilAlongHomBilinearMap_apply]
    exact rationalWeilAlongPolarization_isAlt preservation square universality composition
      unitCoherence associativity comparison symmetry stability compatibility alternation
      hA geometryA MA evaluationA T lam hLam (fun n => Nat.Coprime n m) x

end Langlands.AbelianScheme
