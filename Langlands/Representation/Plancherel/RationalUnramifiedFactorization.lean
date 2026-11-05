import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateAlgebra
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Unique factorization in the actual unramified scalar algebra

Separate one Laurent variable at a time and use polynomial unique factorization
and localization. The published finite Laurent coordinates transport the result
to the evaluation-generated algebra of actual unramified characters.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u v

/-- Splitting off the first exponent turns a finite Laurent algebra into a
one-variable Laurent polynomial ring over the remaining Laurent algebra. -/
def finiteLaurentSuccessorEquiv (R : Type v) [CommRing R] (n : ℕ) :
    AddMonoidAlgebra R (Fin (n + 1) → ℤ) ≃+*
      LaurentPolynomial (AddMonoidAlgebra R (Fin n → ℤ)) :=
  let e : (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) :=
    { toEquiv := (Fin.consEquiv (fun _ : Fin (n + 1) => ℤ)).symm
      map_add' := fun _ _ => rfl }
  (AddMonoidAlgebra.mapDomainRingEquiv R e).trans AddMonoidAlgebra.curryRingEquiv

/-- Laurent localization preserves unique factorization. -/
theorem laurentPolynomial_uniqueFactorizationMonoid
    (R : Type v) [CommRing R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid (LaurentPolynomial R) :=
  UniqueFactorizationMonoid.of_isLocalization
    (Submonoid.powers (Polynomial.X : Polynomial R)) (LaurentPolynomial R)

/-- Finite-rank Laurent algebras over a UFD have unique factorization,
including rank zero. -/
theorem finiteLaurent_uniqueFactorizationMonoid
    (R : Type v) [CommRing R] [UniqueFactorizationMonoid R] (n : ℕ) :
    UniqueFactorizationMonoid (AddMonoidAlgebra R (Fin n → ℤ)) := by
  induction n with
  | zero =>
      exact MulEquiv.uniqueFactorizationMonoid
        (AddMonoidAlgebra.uniqueRingEquiv (R := R) (Fin 0 → ℤ)).symm.toMulEquiv
        inferInstance
  | succ n ih =>
      let := ih
      exact MulEquiv.uniqueFactorizationMonoid
        (finiteLaurentSuccessorEquiv R n).symm.toMulEquiv
        (laurentPolynomial_uniqueFactorizationMonoid
          (AddMonoidAlgebra R (Fin n → ℤ)))

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints G)]
  (hp : Continuous (rationalValuationImageProjection G))
  (hG : GroupScheme.IsConnectedReductive G)

include hp hG

/-- The full actual unramified regular scalar algebra has unique factorization. -/
theorem rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid :
    UniqueFactorizationMonoid
      (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) :=
  MulEquiv.uniqueFactorizationMonoid
    (rationalUnramifiedLaurentAlgebraEquiv G hp hG).toMulEquiv
    (finiteLaurent_uniqueFactorizationMonoid ℂ (rationalImageRank G))

/-- Every nonzero actual regular scalar has a finite prime factorization up to
a unit. This does not assert that its evaluations are everywhere nonzero. -/
theorem rationalUnramifiedRegularFunctions_exists_prime_factors
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hb : b ≠ 0) :
    ∃ factors : Multiset
        (unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)),
      (∀ p ∈ factors, Prime p) ∧ Associated factors.prod b := by
  let := rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid G hp hG
  exact UniqueFactorizationMonoid.exists_prime_factors b hb

end Langlands.Plancherel
