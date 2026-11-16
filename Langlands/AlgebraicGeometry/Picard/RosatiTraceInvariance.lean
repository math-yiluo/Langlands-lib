import Langlands.AlgebraicGeometry.Picard.RosatiPrimeAdjunction
import Langlands.AbelianScheme.Tate.WeilRationalFunctorialityProof
import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyProof
import Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionProof
import Langlands.AbelianScheme.Tate.TwistRankProof
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # The fixed geometric trace is invariant under actual Rosati conjugation -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Rosati

/-- A rational linear operation preserves the fixed actual geometric trace. -/
def PreservesGeometricTrace {k : Type u} [Field k]
    (A : AbelianScheme (Spec (.of k))) (f : End0 A →ₗ[ℚ] End0 A) : Prop :=
  ∀ a : End0 A, geometricEndomorphismTrace A (f a) = geometricEndomorphismTrace A a

/-- Intrinsic traces agree for adjoint operators of a nondegenerate scalar form. -/
theorem trace_eq_of_nondegenerate_adjoint {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (f g : V →ₗ[F] V) (hfg : ∀ x y, B (f x) y = B x (g y)) :
    LinearMap.trace F V f = LinearMap.trace F V g := by
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s F V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    let c := B.dualBasis hB b
    rw [LinearMap.trace_eq_matrix_trace F c, LinearMap.trace_eq_matrix_trace F b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hfg]
    have := b.finiteDimensional_of_finite
    simp only [c, LinearMap.BilinForm.dualBasis, Module.Basis.map_apply,
      LinearMap.BilinForm.apply_toDual_symm_apply, Module.Basis.coe_dualBasis]
    rfl
  · rw [LinearMap.trace, dite_eq_right H]
    rfl

/-- A scalar coordinate on the actual rational Tate twist over an algebraically closed field. -/
theorem rationalTwist_scalar_equiv (k : Type u) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) :
    Nonempty (TateTwist.Rational Γ(Spec (.of k), ⊤) p ≃ₗ[ℚ_[p]] ℚ_[p]) := by
  obtain ⟨e⟩ := TateTwist.integralRankOne k p (inferInstance : IsSepClosed k) hp
  let e0 := (TateTwist.mapEquiv p
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv).trans e.symm
  exact ⟨(e0.baseChange ℤ_[p] ℚ_[p] _ _).trans
    (TensorProduct.AlgebraTensorModule.rid ℤ_[p] ℚ_[p] ℚ_[p])⟩

section GeometricTrace

variable (P : Prerequisites.{u}) {k : Type u} [Field k] [IsAlgClosed k]
  {A : AbelianScheme (Spec (.of k))} (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) (hpol : W.IsPolarization P lam)
  [HasRationalInverse P W lam]

include hpol

/-- The actual prime Tate trace is invariant under the actual geometric Rosati operation. -/
theorem primeEndomorphismTrace_involution (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (a : End0 A) :
    primeEndomorphismTrace A p (involution P W hadd lam a) =
      primeEndomorphismTrace A p a := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  let E := primeRationalWeilAlongHomBilinearMap P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
    W.geometry W.inversePoincare W.evaluation relativeFiniteWeilTransition T p lam
  have hE : E.Nondegenerate := primeRationalPolarizationWeilNondegeneracy
    P.preservation P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability relativeFiniteWeilTransition _ A W.hasDual
    W.geometry W.inversePoincare W.evaluation lam hpol k (𝟙 _) p hp
  obtain ⟨e⟩ := rationalTwist_scalar_equiv k p hp
  let B : LinearMap.BilinForm ℚ_[p] (Tate.PrimeAdic.Rational A T p) :=
    E.compr₂ e.toLinearMap
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      apply hE.1 x
      intro y
      exact e.map_eq_zero_iff.mp (hx y)
    · intro y hy
      apply hE.2 y
      intro x
      exact e.map_eq_zero_iff.mp (hy x)
  have hadj : ∀ x y, B (Tate.PrimeAdic.rationalHomMap T p a x) y =
      B x (Tate.PrimeAdic.rationalHomMap T p (involution P W hadd lam a) y) := by
    intro x y
    exact congrArg e (primeWeil_involution P W hadd relativeFiniteWeilTransition T p
      lam a x y)
  exact (trace_eq_of_nondegenerate_adjoint B hB _ _ hadj).symm

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The fixed rational geometric trace is invariant under the actual Rosati operation. -/
theorem geometricEndomorphismTrace_involution [CharZero k] :
    PreservesGeometricTrace A (involution P W hadd lam) := by
  intro a
  classical
  by_cases h : ∃ T : End0 A →ₗ[ℚ] ℚ,
      ∀ b, algebraMap ℚ ℚ_[2] (T b) = primeEndomorphismTrace A 2 b
  · rw [geometricEndomorphismTrace_eq A h.choose h.choose_spec]
    apply (algebraMap ℚ ℚ_[2]).injective
    rw [h.choose_spec, h.choose_spec]
    exact primeEndomorphismTrace_involution P W hadd lam hpol 2 (by norm_num) a
  · simp only [geometricEndomorphismTrace, dite_eq_right h, LinearMap.zero_apply]

end GeometricTrace

end Langlands.AbelianScheme.Rosati
