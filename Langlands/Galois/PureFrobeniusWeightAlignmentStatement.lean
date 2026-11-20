import Langlands.Galois.CompatibleFamily
import Langlands.Galois.UnitaryNormalization

/-! # Weight alignment for a sum of pure Frobenius systems -/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Polynomial

/-- If the unitary Euler polynomials of a sum of pure actual `λ`-adic
representations agree with those of a single weight, every nonzero summand
has that parity. Integer shifts bring the raw Euler polynomials to the
common weight. -/
def PureFrobeniusWeightAlignmentStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    (ι : L →+* ℂ) (lam : FinitePlace L) (m : ℕ)
    (R : Fin m → LambdaAdic.{uK, uL, uV} K L lam)
    (w : Fin m → ℤ) (P : Fin m → FinitePlace K → L[X])
    (w₀ : ℤ) (P₀ : FinitePlace K → L[X]),
    (∀ᶠ v : FinitePlace K in Filter.cofinite,
      residueCharacteristic v ≠ residueCharacteristic lam →
      (∀ i, HasEulerPolynomialAt (R i) v ((P i v).map (NumberField.FinitePlace.embedding lam)) ∧
        Cohomology.Weights.HasComplexRootsOfWeight (residueCardinality v) (w i)
          ((P i v).reverse.map ι)) ∧
      (P₀ v).coeff 0 = 1 ∧
      Cohomology.Weights.HasComplexRootsOfWeight (residueCardinality v) w₀ ((P₀ v).reverse.map ι) ∧
      unitaryEulerPolynomial ((∏ i, P i v).map ι) = unitaryEulerPolynomial ((P₀ v).map ι)) →
    ∃ a : Fin m → ℤ,
      (∀ i, (R i).val.rank ≠ 0 → w i + 2 * a i = w₀) ∧
      ∀ᶠ v : FinitePlace K in Filter.cofinite,
        residueCharacteristic v ≠ residueCharacteristic lam →
        (∏ i, (P i v).comp (C ((residueCardinality v : L) ^ (a i)) * X)) = P₀ v

end Langlands.GaloisRepresentation
