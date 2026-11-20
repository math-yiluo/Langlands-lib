import Langlands.BaseChange.RegularTransferStatement

/-! # Full finite-place matching for cyclic base change -/

universe u v

set_option autoImplicit false

namespace Langlands.BaseChange

open MeasureTheory Langlands.HarmonicAnalysis

/-- Arthur–Clozel I.3.1 over a cyclic field extension of a characteristic-zero nonarchimedean
local field. All Schwartz–Bruhat tests are allowed, including at singular support. -/
def FinitePlaceFullMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
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
