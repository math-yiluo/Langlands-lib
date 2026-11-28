import Langlands.BaseChange.RegularOrbitalNormalization
import Langlands.JacquetLanglands.DivisionUnits
import Langlands.JacquetLanglands.RegularDivisionParameters

/-! # Normalized regular orbital profiles on a division algebra -/

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory
open Langlands.BaseChange

universe u

/-- The regular units of a central division algebra over a `p`-adic field admit normalized
orbital profiles on the space of reduced characteristic coefficients. -/
def RegularDivisionOrbitalProfileStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D] [TopologicalSpace D] [IsModuleTopology F D],
    letI : IsTopologicalRing D := isTopologicalRing F D
    ∀ [MeasurableSpace Dˣ] [BorelSpace Dˣ] (μ : Measure Dˣ) [μ.IsHaarMeasure],
      ∃ m : RegularOrbitalMeasures (MonoidHom.id Dˣ) μ {a | IsRegular F D a},
        m.IsNormalized ∧ RegularOrbitalProfileData m
          (fun a : {a : Dˣ // IsRegular F D a} => divisionCoefficients F D a.val)

end Langlands.JacquetLanglands
