import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport

/-! # Renard II.3.6: Haar distributions and density embeddings -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardHaar

universe uG

/-- Existence and complex-scalar uniqueness in the full algebraic dual. -/
def LeftHaarStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    ∃ T : Distribution G, IsPositive T ∧ IsLeftInvariant T ∧
      ∀ S : Distribution G, IsLeftInvariant S → ∃! c : ℂ, S = c • T

/-- The analogous right-invariant distribution assertion. -/
def RightHaarStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    ∃ T : Distribution G, IsPositive T ∧ IsRightInvariant T ∧
      ∀ S : Distribution G, IsRightInvariant S → ∃! c : ℂ, S = c • T

/-- Strictly positive invariant distributions differ by a positive real scalar. -/
def PositiveScalarUniquenessStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (T S : Distribution G), IsPositive T → IsPositive S →
    ((IsLeftInvariant T ∧ IsLeftInvariant S) ∨
      (IsRightInvariant T ∧ IsRightInvariant S)) →
    ∃! c : ℝ, 0 < c ∧ S = (c : ℂ) • T

/-- The original algebraic-dual assertion is realized by actual Mathlib Haar
integration, including comparison with every invariant algebraic distribution. -/
def MeasureHaarBridgeStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    IsPositive (ofMeasure μ) ∧ IsLeftInvariant (ofMeasure μ) ∧
      ∀ T : Distribution G, IsLeftInvariant T →
        ∃! c : ℂ, T = c • ofMeasure μ

/-- The concrete density map is injective and preserves support; its restriction
to tests has compactly supported values in the existing E′ submodule. -/
def DensityEmbeddingStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    Function.Injective (density μ) ∧
      (∀ f : LocallyConstant G ℂ,
        support (density μ f) = Function.support f) ∧
      ∀ f : SchwartzBruhat G, testDensity μ f ∈ compactlySupported

/-- The focused II.3.6 statement family. -/
def Statements : Prop :=
  LeftHaarStatement.{uG} ∧ RightHaarStatement.{uG} ∧
    PositiveScalarUniquenessStatement.{uG} ∧ MeasureHaarBridgeStatement.{uG} ∧
    DensityEmbeddingStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardHaar
