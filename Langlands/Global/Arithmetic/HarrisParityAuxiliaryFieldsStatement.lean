import Langlands.Galois.QuadraticPatchingStatement
import Mathlib.NumberTheory.NumberField.CMField

/-! # Quadratic CM auxiliary fields for Harris's parity argument -/

noncomputable section

universe uE

namespace Langlands.Global.Harris

open NumberField AdelicFunctoriality.FiniteExtension

/-- A quadratic extension which doubles the totally real degree and keeps the
original imaginary quadratic factor. -/
def IsParityAuxiliary {E : Type uE} [Field E] [NumberField E]
    (E₀ K₀ : IntermediateField ℚ E)
    (N : FiniteGaloisIntermediateField E (AlgebraicClosure E)) : Prop :=
  Module.finrank E N = 2 ∧ IsCMField N ∧
    ∃ N₀ : IntermediateField ℚ N,
      E₀.map (IsScalarTower.toAlgHom ℚ E N) ≤ N₀ ∧
      IsTotallyReal N₀ ∧
      Module.finrank ℚ N₀ = 2 * Module.finrank ℚ E₀ ∧
      N₀ ⊔ K₀.map (IsScalarTower.toAlgHom ℚ E N) = ⊤

/-- Supply of quadratic CM parity auxiliaries with prescribed split places.
The first conclusion supplies disjoint auxiliaries for patching. The second
supplies three auxiliaries covering almost all places by complete splitting. -/
def HarrisParityAuxiliaryFieldsStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    ∀ V : Finset (FinitePlace E),
      (∀ M : FiniteGaloisIntermediateField E (AlgebraicClosure E),
        ∃ N : FiniteGaloisIntermediateField E (AlgebraicClosure E),
          N ⊓ M = ⊥ ∧ IsParityAuxiliary E₀ K₀ N ∧
          letI : NumberField N := NumberField.of_module_finite E N
          ∀ v ∈ V, SplitsCompletelyAt (N := N) v) ∧
      ∃ (N : Fin 3 → FiniteGaloisIntermediateField E (AlgebraicClosure E))
        (T : Finset (FinitePlace E)),
        Function.Injective N ∧
        (∀ i, IsParityAuxiliary E₀ K₀ (N i) ∧
          letI : NumberField (N i) := NumberField.of_module_finite E (N i)
          ∀ v ∈ V, SplitsCompletelyAt (N := N i) v) ∧
        ∀ v ∉ T, ∃ i,
          letI : NumberField (N i) := NumberField.of_module_finite E (N i)
          SplitsCompletelyAt (N := N i) v

end Langlands.Global.Harris
