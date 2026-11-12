import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.GroupFunctionSpaces
import Langlands.Representation.Hecke.Convolution

/-! # Renard II.3.12: uniform distributions and the discrete exceptions -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity

universe uG

/-- The actual density embedding has precisely the three uniform compact
invariance ranges occurring in the source's Lemma. -/
def UniformRangeStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    Function.Injective (testDensity μ) ∧
      (LinearMap.range (testDensity μ) : Set (Distribution G)) =
        GroupFunctionSpaces.uniformCompactDistributionsLeft ∧
      GroupFunctionSpaces.uniformCompactDistributionsLeft (G := G) =
        GroupFunctionSpaces.uniformCompactDistributionsRight ∧
      GroupFunctionSpaces.uniformCompactDistributionsLeft (G := G) =
        GroupFunctionSpaces.uniformCompactDistributionsBoth

/-- The corrected exact criterion for the printed exclusion of Dirac from H(G). -/
def DiracMembershipStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (g : G),
    dirac g ∈ LinearMap.range (testDensity μ) ↔ DiscreteTopology G

/-- The function realization of the Hecke algebra has a two-sided convolution
identity exactly in the discrete case. -/
def UnitCriterionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    (∃ e : Hecke.HeckeAlgebra μ, ∀ h : Hecke.HeckeAlgebra μ,
      e * h = h ∧ h * e = h) ↔ DiscreteTopology G

/-- The density range is a two-sided ideal in the original compact distribution
convolution algebra. Compact subtype witnesses are constrained to the density. -/
def IdealStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : compactlySupported (X := G)) (D : Distribution G),
    D ∈ LinearMap.range (testDensity μ) →
    ∃ F : compactlySupported (X := G), (F : Distribution G) = D ∧
      (convolution T F : Distribution G) ∈ LinearMap.range (testDensity μ) ∧
      (convolution F T : Distribution G) ∈ LinearMap.range (testDensity μ)

/-- The inversion anti-involution's exact function realization, including the
modular density factor for a general t.d. group. -/
def InversionDensityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (f : SchwartzBruhat G),
    ∃ g : SchwartzBruhat G,
      (∀ x : G, g x = (((renardModular x : ℝ)⁻¹) : ℂ) * f x⁻¹) ∧
      GroupAction.inversionDistributions (testDensity μ f) = testDensity μ g

def Statements : Prop :=
  UniformRangeStatement.{uG} ∧ DiracMembershipStatement.{uG} ∧
    UnitCriterionStatement.{uG} ∧ IdealStatement.{uG} ∧
    InversionDensityStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity
