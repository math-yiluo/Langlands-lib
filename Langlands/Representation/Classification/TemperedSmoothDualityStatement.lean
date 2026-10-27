import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Smooth.Contragredient.Definitions

/-!
# Analytic temperedness and the smooth contragredient: proposition target

This module states, and does not prove, that the actual smooth contragredient
of an admissible complex representation of positive-rank p-adic `GL_n(F)`
is tempered exactly when the representation is. Temperedness is the imported
predicate over all Borel Haar measures on the actual central quotient.
-/

namespace Langlands.Classification

universe uF uV

/-- For every prime, p-adic field, compatible topological realization, positive
rank and admissible complex representation `ρ` of `GL_n(F)`, the smooth
contragredient of `ρ` is analytically tempered exactly when `ρ` is. -/
def PadicTemperedSmoothDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      IsAdmissible ρ →
        (T.IsTempered (smoothContragredient ρ) ↔ T.IsTempered ρ)

end Langlands.Classification
