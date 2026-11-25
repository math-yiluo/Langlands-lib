import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: matching of test functions near the identity for a cyclic algebra

For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` (a
commutative ring, not necessarily a field) with generator `σ` of order `l`
(`IsCyclicAlgebra σ l`), `n : ℕ` and Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`: there
is a neighbourhood `U` of `1` in `GL_n(E)` such that every Schwartz–Bruhat function supported in
`U` has a concordant Schwartz–Bruhat function on `GL_n(F)`, and a neighbourhood `V` of `1` in
`GL_n(F)` such that every Schwartz–Bruhat function supported in `V` has a concordant
Schwartz–Bruhat function on `GL_n(E)`. It is `NearIdentityMatchingStatement` with `[CommRing E]`
in place of `[Field E]`.

This is a statement only; it is proved in `CyclicAlgebraNearIdentityMatching.lean`.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- Matching near the identity, for a cyclic algebra. -/
def CyclicAlgebraNearIdentityMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
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
