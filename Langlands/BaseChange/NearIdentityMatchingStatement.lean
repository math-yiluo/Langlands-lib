import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: matching of test functions near the identity for cyclic base change

For a nonarchimedean local field `F` of characteristic zero, a cyclic field extension `E` of `F`
with generator `σ` of order `l` (`IsCyclicAlgebra σ l`), `n : ℕ` and Haar measures `μF` on
`GL_n(F)` and `μE` on `GL_n(E)`: there is a neighbourhood `U` of `1` in `GL_n(E)` such that every
Schwartz–Bruhat function supported in `U` has a concordant Schwartz–Bruhat function on `GL_n(F)`,
and a neighbourhood `V` of `1` in `GL_n(F)` such that every Schwartz–Bruhat function supported in
`V` has a concordant Schwartz–Bruhat function on `GL_n(E)` (Arthur–Clozel, Chapter 1,
Proposition 3.1, near the identity; concordance in the sense of Henniart–Lemaire, I.2.5).

This is a statement only; it is proved in `NearIdentityMatching.lean`.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- Matching near the identity, for a cyclic extension of fields. -/
def NearIdentityMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
      (∃ U ∈ nhds (1 : GeneralLinear n E), ∀ φ : SchwartzBruhat (GeneralLinear n E),
        Function.support φ ⊆ U →
        ∃ f : SchwartzBruhat (GeneralLinear n F), AreConcordant σ l μF μE φ f) ∧
      (∃ V ∈ nhds (1 : GeneralLinear n F), ∀ f : SchwartzBruhat (GeneralLinear n F),
        Function.support f ⊆ V →
        ∃ φ : SchwartzBruhat (GeneralLinear n E), AreConcordant σ l μF μE φ f)

end Langlands.BaseChange
