import Langlands.AlgebraicGeometry.Picard.RosatiTraceInvariance
import Langlands.AbelianScheme.Tate.WeilRationalPolarizationAlternationProof
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationProof

/-! # Symmetry of the fixed actual Rosati trace form -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme.Rosati

private theorem trace_mul_adjoint_swap {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (hAlt : B.IsAlt) (f fd g gd : V →ₗ[F] V)
    (hf : ∀ x y, B (f x) y = B x (fd y))
    (hg : ∀ x y, B (g x) y = B x (gd y)) :
    LinearMap.trace F V (f * gd) = LinearMap.trace F V (g * fd) := by
  apply trace_eq_of_nondegenerate_adjoint B hB
  intro x y
  change B (f (gd x)) y = B x (g (fd y))
  rw [hf]
  calc
    B (gd x) (fd y) = -B (fd y) (gd x) := (hAlt.neg_eq _ _).symm
    _ = -B (g (fd y)) x := by rw [hg]
    _ = B x (g (fd y)) := hAlt.neg_eq _ _

section GeometricTrace

variable (P : Prerequisites.{u}) {k : Type u} [Field k] [IsAlgClosed k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
  (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) (hpol : W.IsPolarization P lam)
  [HasRationalInverse P W lam]

include hpol

/-- The actual prime Tate traces of the two Rosati products agree. -/
theorem primeEndomorphismTrace_rosati_swap (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (a b : End0 A) :
    primeEndomorphismTrace A p (a * involution P W hadd lam b) =
      primeEndomorphismTrace A p (b * involution P W hadd lam a) := by
  let T : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) := Over.mk (𝟙 _)
  let E := primeRationalWeilAlongHomBilinearMap P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability W.hasDual
    W.geometry W.inversePoincare W.evaluation relativeFiniteWeilTransition T p lam
  have hE : E.Nondegenerate := primeRationalPolarizationWeilNondegeneracy
    P.preservation P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability relativeFiniteWeilTransition _ A W.hasDual
    W.geometry W.inversePoincare W.evaluation lam hpol k (𝟙 _) p hp
  have hAlt : E.IsAlt := primeRationalWeilAlongPolarization_isAlt
    P.preservation P.square P.universality P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry P.stability relativeFiniteWeilTransition
    relativeFiniteWeilAlternation W.hasDual W.geometry W.inversePoincare W.evaluation
    T lam hpol p
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
  have hBAlt : B.IsAlt := by
    intro x
    change e (E x x) = 0
    rw [hAlt x, map_zero]
  have hadj : ∀ (c : End0 A) x y,
      B (Tate.PrimeAdic.rationalHomMap T p c.asHom x) y =
        B x (Tate.PrimeAdic.rationalHomMap T p (involution P W hadd lam c).asHom y) := by
    intro c x y
    exact congrArg e (primeWeil_involution P W hadd relativeFiniteWeilTransition T p
      lam c x y)
  change LinearMap.trace ℚ_[p] _
      ((Tate.PrimeAdic.rationalEndAction T p A) (a * involution P W hadd lam b)) =
    LinearMap.trace ℚ_[p] _
      ((Tate.PrimeAdic.rationalEndAction T p A) (b * involution P W hadd lam a))
  rw [map_mul (Tate.PrimeAdic.rationalEndAction T p A),
    map_mul (Tate.PrimeAdic.rationalEndAction T p A)]
  exact trace_mul_adjoint_swap B hB hBAlt _ _ _ _ (hadj a) (hadj b)

/-- The fixed rational trace form is symmetric for an actual geometric polarization. -/
theorem traceForm_symm [CharZero k] (a b : End0 A) :
    traceForm (k := k) P W hadd lam a b = traceForm (k := k) P W hadd lam b a := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [traceForm_apply, traceForm_apply]
  by_cases h : ∃ T : End0 A →ₗ[ℚ] ℚ,
      ∀ c, algebraMap ℚ ℚ_[2] (T c) = primeEndomorphismTrace A 2 c
  · rw [geometricEndomorphismTrace_eq A h.choose h.choose_spec]
    apply (algebraMap ℚ ℚ_[2]).injective
    rw [h.choose_spec, h.choose_spec]
    exact primeEndomorphismTrace_rosati_swap P W hadd lam hpol 2 (by norm_num) a b
  · simp only [geometricEndomorphismTrace, dite_eq_right h, LinearMap.zero_apply]

end GeometricTrace

/-- Full-universe symmetry of the already defined actual Rosati trace form. -/
def TraceFormSymmetryStatement : Prop :=
  ∀ (P : Prerequisites.{u})
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P),
    W.IsPolarization P lam →
    ∀ [HasRationalInverse P W lam],
      ∀ a b : End0 A,
        traceForm (k := k) P W hadd lam a b = traceForm (k := k) P W hadd lam b a

/-- The actual alternating polarization pairing proves trace-form symmetry. -/
theorem traceFormSymmetry : TraceFormSymmetryStatement.{u} := by
  intro P k _ _ _ A W hadd lam hpol _ a b
  exact traceForm_symm P W hadd lam hpol a b

end Langlands.AbelianScheme.Rosati
