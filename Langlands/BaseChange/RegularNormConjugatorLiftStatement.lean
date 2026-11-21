import Langlands.BaseChange.Norm

/-! # Lifting a twisted conjugator with regular cyclic norm -/

namespace Langlands.BaseChange

universe u v w

/-- A twisted conjugator lifts through a surjective equivariant coefficient map
that reflects units when the cyclic norms share a characteristic polynomial over
the fixed base, its derivative evaluated on the reduced norm is invertible,
and the cyclic degree is a unit in the target ring. -/
def RegularNormConjugatorLiftStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (T : Type w) [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) [IsLocalHom f.toRingHom],
    Function.Surjective f →
    ∀ (σ : S ≃ₐ[R] S) (τ : T ≃ₐ[R] T) (l n : ℕ), σ ^ l = 1 →
      (∀ a : S, f (σ a) = τ (f a)) →
      ∀ (p : Polynomial R) (δ δ' : GeneralLinear n S),
        (cyclicNorm σ l δ).val.charpoly = p.map (algebraMap R S) →
        (cyclicNorm σ l δ').val.charpoly = p.map (algebraMap R S) →
        IsUnit (l : T) →
        IsUnit (Polynomial.aeval
          (cyclicNorm τ l (Matrix.GeneralLinearGroup.map f.toRingHom δ)).val
          (p.map (algebraMap R T)).derivative) →
        (∃ x : GeneralLinear n T,
          x⁻¹ * Matrix.GeneralLinearGroup.map f.toRingHom δ * entrywiseAut τ n x =
            Matrix.GeneralLinearGroup.map f.toRingHom δ') →
        ∃ x : GeneralLinear n S, x⁻¹ * δ * entrywiseAut σ n x = δ'

end Langlands.BaseChange
