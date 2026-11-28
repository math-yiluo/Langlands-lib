import Langlands.JacquetLanglands.DivisionMatching
import Langlands.JacquetLanglands.DivisionUnits

/-! # Haar integrals of matching regular-supported functions -/

namespace Langlands.JacquetLanglands

open MeasureTheory
open Langlands.BaseChange (IsEllipticSupported)

universe u

/-- For matching, Haar-integrable functions supported in the regular elliptic set of
`GL_n(F)` and the regular set of `Dˣ`, the two Haar integrals agree. The central division
algebra `D` has dimension `n²`, the Borel structures are used on both groups, and the
ambient Haar measures may be chosen independently. -/
def DivisionMatchingIntegralStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D] (n : ℕ),
    Module.finrank F D = n ^ 2 →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace Dˣ := borel _
    haveI : BorelSpace Dˣ := ⟨rfl⟩
    haveI := Langlands.JacquetLanglands.isTopologicalRing F D
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
      (μ' : Measure Dˣ) [μ'.IsHaarMeasure] (f : GeneralLinear n F → ℂ) (f' : Dˣ → ℂ),
      IsEllipticSupported f → IsDivisionRegularSupported F D f' →
      Integrable f μ → Integrable f' μ' → AreMatching μ μ' f f' →
      (∫ g, f g ∂μ) = ∫ g', f' g' ∂μ'

end Langlands.JacquetLanglands
