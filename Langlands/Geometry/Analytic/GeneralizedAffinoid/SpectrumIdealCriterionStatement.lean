import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach

/-! # Spectrum criteria for proper ideals and units at arbitrary positive radii -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Every actual proper ideal is annihilated by a bounded spectrum point.
No closedness premise or chosen point is supplied. -/
def SpectrumProperIdealStatement [CompleteSpace K] : Prop :=
  ∀ (P : PresentedAffinoidAlgebra K) (I : Ideal P),
    I ≠ ⊤ → ∃ x : BanachSpectrum P, I ≤ x.kernel

/-- An element is a unit exactly when no bounded spectrum point annihilates it. -/
def SpectrumUnitStatement [CompleteSpace K] : Prop :=
  ∀ (P : PresentedAffinoidAlgebra K) (a : P),
    IsUnit a ↔ ∀ x : BanachSpectrum P, x a ≠ 0

/-- A finite tuple generates the unit ideal exactly when it has no common
zero in the bounded spectrum. This includes the empty tuple. -/
def SpectrumFiniteUnitIdealStatement [CompleteSpace K] : Prop :=
  ∀ (P : PresentedAffinoidAlgebra K) (m : ℕ) (f : Fin m → P),
    Ideal.span (Set.range f) = ⊤ ↔ ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0

/-- The proper-ideal realization and its unit and finite-generator criteria
for all actual finite positive-polyradius affinoid quotient presentations. -/
def SpectrumIdealCriterionStatement [CompleteSpace K] : Prop :=
  SpectrumProperIdealStatement K ∧ SpectrumUnitStatement K ∧
    SpectrumFiniteUnitIdealStatement K

end Langlands.Analytic.PresentedAffinoidAlgebra
