import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Transfer of test functions with regular support

Henniart–Lemaire (2011), Chapter I, §I.2.5, Proposition (printed p. 18): for a
nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of degree `l`
with generator `σ`, and Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`:

* (1) every Schwartz–Bruhat function `φ` on `GL_n(E)` supported in the σ-regular set has a
  concordant Schwartz–Bruhat function `f` on `GL_n(F)` supported in the regular set;
* (2) every Schwartz–Bruhat function `f` on `GL_n(F)` supported in the regular set whose
  orbital integrals vanish at regular non-norms has a concordant Schwartz–Bruhat function
  `φ` on `GL_n(E)` supported in the σ-regular set.

This is a statement only; it is not proved here.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory
open Langlands.QuotientIntegration
open Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- HL I.2.5, Proposition (printed p. 18), in characteristic zero: transfer between
σ-regularly supported and regularly supported Schwartz–Bruhat functions. -/
def RegularTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
      (∀ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaRegularSupported σ l φ →
        ∃ f : SchwartzBruhat (GeneralLinear n F), IsRegularSupported f ∧
          AreConcordant σ l μF μE φ f) ∧
      (∀ f : SchwartzBruhat (GeneralLinear n F), IsRegularSupported f →
        VanishesOffNorms σ l μF f →
        ∃ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaRegularSupported σ l φ ∧
          AreConcordant σ l μF μE φ f)

end Langlands.BaseChange
