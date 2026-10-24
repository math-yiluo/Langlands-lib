import Langlands.ClassField.Global.LocalUnitCohomology
import Langlands.ClassFieldTheory.Local.CohomologyExistence

/-! # Cohomology of the valuation units of number-field completions

Statements only: the Herbrand quotient of the valuation units `U_w` of a cyclic extension of
completions `E_w / F_v` is `1`, and both `H¹` and `H²` of `U_w` vanish when `w` is unramified
over `v`. A third statement records that these follow from local cohomology existence.
-/

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

/-- `h(U_w) = 1`: for a Galois extension of number fields `E / F`, a finite place `w` of `E`
over `v`, and a cyclic local Galois group `Gal(E_w / F_v)`, the ordinary first and second
cohomology groups of the valuation units `U_w` are finite and have the same order. -/
def CyclicCompletionUnitHerbrand : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal]
    [IsCyclic (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E)],
    Finite (groupCohomology (localUnitsRepresentation v w) 1 : Type u) ∧
      Finite (groupCohomology (localUnitsRepresentation v w) 2 : Type u) ∧
      Nat.card (groupCohomology (localUnitsRepresentation v w) 2 : Type u) =
        Nat.card (groupCohomology (localUnitsRepresentation v w) 1 : Type u)

/-- At a finite place `w` of `E` unramified over `v`, for `E / F` Galois, the ordinary first
and second cohomology groups of the valuation units `U_w` under `Gal(E_w / F_v)` are
trivial. -/
def UnramifiedCompletionUnitVanishing : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal],
    w.asIdeal.ramificationIdx (𝓞 F) = 1 →
      Subsingleton (groupCohomology (localUnitsRepresentation v w) 1 : Type u) ∧
        Subsingleton (groupCohomology (localUnitsRepresentation v w) 2 : Type u)

/-- Local cohomology existence implies both statements above. -/
def CompletionUnitHerbrandFromCohomologyExistence : Prop :=
  Langlands.ClassFieldTheory.Local.CohomologyExistence.{u, u} →
    CyclicCompletionUnitHerbrand.{u} ∧ UnramifiedCompletionUnitVanishing.{u}

end Langlands.ClassField.Global
