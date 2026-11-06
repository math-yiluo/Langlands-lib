import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]

/-- A chosen size of a finite generating family of the original coefficient algebra. -/
def finiteAlgebraFiberBound : ℕ :=
  Classical.choose (Module.Finite.exists_fin' A B)

/-- The original finite generating family is a quotient of this many free coordinates. -/
theorem finiteAlgebraFiberBound_surjection :
    ∃ f : (Fin (finiteAlgebraFiberBound A B) → A) →ₗ[A] B, Function.Surjective f :=
  Classical.choose_spec (Module.Finite.exists_fin' A B)

/-- Every field base change has dimension at most the chosen original generator bound. -/
theorem finiteAlgebraFiberBound_finrank (C : Type u) [Field C] [Algebra A C] :
    Module.finrank C (C ⊗[A] B) ≤ finiteAlgebraFiberBound A B := by
  obtain ⟨f, hf⟩ := finiteAlgebraFiberBound_surjection A B
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := f.baseChange C) (LinearMap.baseChange_surjective C hf)
  have he : Module.finrank C (C ⊗[A] (Fin (finiteAlgebraFiberBound A B) → A)) =
      finiteAlgebraFiberBound A B := by
    rw [(TensorProduct.piScalarRight A C C (Fin (finiteAlgebraFiberBound A B))).finrank_eq]
    simp
  exact h.trans he.le

private theorem primeSpectrum_card_le_finrank (C R : Type u) [Field C] [CommRing R]
    [Algebra C R] [Module.Finite C R] : Nat.card (PrimeSpectrum R) ≤ Module.finrank C R := by
  classical
  let : IsArtinianRing R := isArtinian_of_tower C inferInstance
  let : Fintype (PrimeSpectrum R) := Fintype.ofFinite _
  let : ∀ p : PrimeSpectrum R, Module.Finite C (Localization.AtPrime p.asIdeal) :=
    fun p => Module.Finite.of_surjective
      (Algebra.algHom C R (Localization.AtPrime p.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
  rw [Nat.card_eq_fintype_card, IsArtinianRing.finrank_eq_sum_primeSpectrum R C]
  calc
    Fintype.card (PrimeSpectrum R) = ∑ _p : PrimeSpectrum R, 1 := by simp
    _ ≤ ∑ p : PrimeSpectrum R, Module.finrank C (Localization.AtPrime p.asIdeal) := by
      exact Finset.sum_le_sum fun p _ => Nat.succ_le_of_lt (Module.finrank_pos :
        0 < Module.finrank C (Localization.AtPrime p.asIdeal))

/-- The same generator bound controls every original prime of every field coefficient fiber. -/
theorem finiteAlgebraFiberBound_card (C : Type u) [Field C] [Algebra A C] :
    Nat.card (PrimeSpectrum (C ⊗[A] B)) ≤ finiteAlgebraFiberBound A B :=
  (primeSpectrum_card_le_finrank C (C ⊗[A] B)).trans
    (finiteAlgebraFiberBound_finrank A B C)

end Langlands.AlgebraicGeometry
