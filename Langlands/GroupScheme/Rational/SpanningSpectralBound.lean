import Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites
import Langlands.GroupScheme.Rational.MatrixEntryBoundedCompactnessStatement
import Langlands.LinearAlgebra.ValuativeTraceBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Spectral entry bounds when actual rational matrices span -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open ValuativeRel
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {F : Type u} [Field F] [ValuativeRel F]
  {G : GroupScheme (Spec (CommRingCat.of F))} {N : ℕ}

/-- The actual rational matrices span the whole matrix algebra as a vector space. -/
def HasFullRationalMatrixSpan (ρ : MatrixRepresentation G (Fin N)) : Prop :=
  Submodule.span F (Set.range fun g : rationalPoints G =>
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F)) = ⊤

/-- Integral characteristic coefficients bound the trace, also in dimension zero. -/
theorem trace_vle_one_of_integralCharacteristicPolynomials
    (ρ : MatrixRepresentation G (Fin N))
    (hint : ρ.HasIntegralCharacteristicPolynomials) (g : rationalPoints G) :
    (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F).trace ≤ᵥ (1 : F) := by
  cases isEmpty_or_nonempty (Fin N) with
  | inl h => simp [Matrix.trace, zero_vle]
  | inr h =>
    rw [Matrix.trace_eq_neg_charpoly_coeff]
    apply (ValuativeRel.valuation F).vle_iff_le.mpr
    simpa only [Valuation.map_neg] using
      (ValuativeRel.valuation F).vle_iff_le.mp (hint g (Fintype.card (Fin N) - 1))

/-- Traces of products of actual rational matrices are integral. -/
theorem trace_mul_vle_one_of_integralCharacteristicPolynomials
    (ρ : MatrixRepresentation G (Fin N))
    (hint : ρ.HasIntegralCharacteristicPolynomials) (g h : rationalPoints G) :
    ((ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F) *
      (ρ.rationalMatrix h : Matrix (Fin N) (Fin N) F)).trace ≤ᵥ (1 : F) := by
  simpa only [map_mul, Matrix.GeneralLinearGroup.coe_mul] using
    ρ.trace_vle_one_of_integralCharacteristicPolynomials hint (g * h)

/-- Full rational matrix span supplies the trace probes needed for a common
bound on every actual rational matrix entry. -/
theorem hasUniformlyBoundedEntries_of_fullSpan
    (ρ : MatrixRepresentation G (Fin N)) (hspan : ρ.HasFullRationalMatrixSpan)
    (hint : ρ.HasIntegralCharacteristicPolynomials) :
    ρ.HasUniformlyBoundedEntries := by
  let S : Set (Matrix (Fin N) (Fin N) F) :=
    Set.range fun g : rationalPoints G => (ρ.rationalMatrix g : Matrix (Fin N) (Fin N) F)
  obtain ⟨b, hb, h⟩ := exists_valuative_bound_entries_of_trace_vle_one S S hspan (by
    rintro B ⟨h, rfl⟩ A ⟨g, rfl⟩
    exact ρ.trace_mul_vle_one_of_integralCharacteristicPolynomials hint g h)
  exact ⟨b, hb, fun g i j => h _ ⟨g, rfl⟩ i j⟩

end Langlands.GroupScheme.MatrixRepresentation
