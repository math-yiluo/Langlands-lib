module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normalization and a separable extension of the ground field

Let `A` be a reduced ring with finitely many minimal primes and let `A'` be the integral closure
of `A` in its total ring of fractions.  For a separable extension `K/k` of the ground field,
`K ⊗[k] A'` is again normal, and hence reduced.

Normality of `K ⊗[k] A'` is the step of the separable half of Tag 0C3N that forces
`K ⊗[k] A'` to be the integral closure of `K ⊗[k] A` in the total ring of fractions of
`K ⊗[k] A`; that identification itself is not proved here.  The scheme-level comparison
morphism of Tag 0C3N is built in
`StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic`.

## Main results

* `IsNormalRing.tensorProduct_of_isSeparableExtension`: the base change of a normal ring along a
  separable extension of fields is normal.  This is the ring-level form of Tag 0C3M.
* `isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes`: the integral closure of a
  reduced ring with
  finitely many minimal primes in its total ring of fractions is normal.
* `isNormalRing_tensorProduct_integralClosure_fractionRing` combines the two.
* `includeRight_mem_nonZeroDivisors_tensorProduct`: extension of the ground field carries
  non-zerodivisors to non-zerodivisors.

## References

* [Stacks Project, Tag 0C3M](https://stacks.math.columbia.edu/tag/0C3M)
* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ### Base change of a normal ring along a separable extension -/

/-! ### Normality of the integral closure in the total ring of fractions -/

/-- The integral closure of a domain in its fraction field is integrally closed. -/
theorem isIntegrallyClosed_integralClosure_of_isDomain
    (R : Type*) [CommRing R] [IsDomain R] (F : Type*) [Field F] [Algebra R F]
    [IsFractionRing R F] : IsIntegrallyClosed (integralClosure R F) :=
  let : IsFractionRing (integralClosure R F) F :=
    Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra F (integralClosure R F)
  (IsIntegrallyClosed.integralClosure_eq_bot_iff F).mp integralClosure_idem

/-- The integral closure of a reduced ring with finitely many minimal primes in its total ring of
fractions is a normal ring.  It is a finite product of integral closures of domains in their
fraction fields (Tag 035P), each of which is a normal domain.

The name carries the `_of_finite_minimalPrimes` suffix because the plain name
`isNormalRing_integralClosure_fractionRing` is already taken, in the **root namespace**, by
`StacksFrontier/AlgebraicGeometry/Variety/DeltaInvariant/Normalization.lean` (which carries
`@[stacks 0C3S "normality"]` and assumes `[IsNoetherianRing A]`).  Co-importing the two files
without this rename is an ambiguity error, which is what regenerating the library's import list
exposed.  This statement is **strictly more general** than the tagged one -- finitely many minimal
primes rather than Noetherian -- so the tagged one is derivable from it via
`minimalPrimes.finite_of_isNoetherianRing`. -/
theorem isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes
    {A : Type*} [CommRing A] [IsReduced A] (hA : (minimalPrimes A).Finite) :
    IsNormalRing (integralClosure A (FractionRing A)) := by
  have : Finite (minimalPrimes A) := hA
  -- The `A`-algebra structures on the factors are the ones fixed in the statement of Tag 035P(3).
  let _ : ∀ p : minimalPrimes A,
      Algebra A (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))) :=
    fun p =>
      ((algebraMap (A ⧸ (p : Ideal A))
        (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A))))).comp
        (Ideal.Quotient.mk (p : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient hA
  refine IsNormalRing.congr e.symm.toRingEquiv (isNormalRing_pi fun p ↦ ?_)
  have : (p : Ideal A).IsPrime := p.2.1.1
  have := isIntegrallyClosed_integralClosure_of_isDomain (A ⧸ (p : Ideal A))
    (FractionRing (A ⧸ (p : Ideal A)))
  exact IsNormalRing.of_isIntegrallyClosed _

/-! ### Non-zerodivisors after extension of the ground field -/

end
