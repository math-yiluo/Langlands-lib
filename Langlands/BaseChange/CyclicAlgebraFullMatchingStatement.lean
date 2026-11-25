import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: full finite-place matching for a cyclic algebra

`FinitePlaceFullMatchingStatement` with `[CommRing E]` in place of `[Field E]`: for a
nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` with generator `σ`
of order `l` (`IsCyclicAlgebra σ l`), `n : ℕ` and Haar measures `μF` on `GL_n(F)` and `μE` on
`GL_n(E)`, every Schwartz–Bruhat function on `GL_n(E)` has a concordant Schwartz–Bruhat function
on `GL_n(F)`, and every Schwartz–Bruhat function on `GL_n(F)` whose orbital integrals vanish at
the regular semisimple non-norms has a concordant Schwartz–Bruhat function on `GL_n(E)`.

This is a statement only; `CyclicAlgebraFullMatching.lean` proves that it follows from
`FinitePlaceFullMatchingStatement`.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- Full finite-place matching (Arthur–Clozel I.3.1), for a cyclic algebra. -/
def CyclicAlgebraFullMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
      (∀ φ : SchwartzBruhat (GeneralLinear n E),
        ∃ f : SchwartzBruhat (GeneralLinear n F), AreConcordant σ l μF μE φ f) ∧
      (∀ f : SchwartzBruhat (GeneralLinear n F), VanishesOffNorms σ l μF f →
        ∃ φ : SchwartzBruhat (GeneralLinear n E), AreConcordant σ l μF μE φ f)

end Langlands.BaseChange
