import Langlands.HarmonicAnalysis.Distribution.HeckeRealization
import Langlands.HarmonicAnalysis.Distribution.Convolution

/-! # Renard II.3.13: the full-distribution Hecke actions -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardFullHecke

universe uG

/-- The two source kernels, with integrability and actual test witnesses. -/
def KernelStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G),
    (∀ x : G, Integrable (fun y => h y * f (x * y)) μ ∧
      Integrable (fun y => h y * f (y * x)) μ) ∧
    ∃ r l : SchwartzBruhat G,
      (∀ x : G, r x = ∫ y, h y * f (x * y) ∂μ) ∧
      (∀ x : G, l x = ∫ y, h y * f (y * x) ∂μ) ∧
      ∀ T : Distribution G,
        rightHeckeConvolution μ T h f = T r ∧
        leftHeckeConvolution μ h T f = T l

/-- Agreement with compact convolution, on the existing density realization. -/
def CompactCompatibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : compactlySupported (X := G)) (h : Hecke.HeckeAlgebra μ),
    ∃ H : compactlySupported (X := G),
      (H : Distribution G) = heckeDistribution μ h ∧
      rightHeckeConvolution μ (T : Distribution G) h =
        (convolution T H : Distribution G) ∧
      leftHeckeConvolution μ h (T : Distribution G) =
        (convolution H T : Distribution G)

/-- Inversion uses the actual inverted density, including its modular factor. -/
def InversionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (h : Hecke.HeckeAlgebra μ),
    ∃ hi : Hecke.HeckeAlgebra μ,
      heckeDistribution μ hi =
        GroupAction.inversionDistributions (heckeDistribution μ h) ∧
      ∀ T : Distribution G,
        GroupAction.inversionDistributions (rightHeckeConvolution μ T h) =
          leftHeckeConvolution μ hi (GroupAction.inversionDistributions T) ∧
        GroupAction.inversionDistributions (leftHeckeConvolution μ h T) =
          rightHeckeConvolution μ (GroupAction.inversionDistributions T) hi

/-- The right associativity exercise and its left and mixed counterparts. -/
def AssociativityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : Distribution G) (h k : Hecke.HeckeAlgebra μ),
    rightHeckeConvolution μ T (h * k) =
      rightHeckeConvolution μ (rightHeckeConvolution μ T h) k ∧
    leftHeckeConvolution μ (h * k) T =
      leftHeckeConvolution μ h (leftHeckeConvolution μ k T) ∧
    leftHeckeConvolution μ h (rightHeckeConvolution μ T k) =
      rightHeckeConvolution μ (leftHeckeConvolution μ h T) k

/-- The equivalent evaluation definition (II.3.13.1), using the original scalar
distribution/test convolution at the identity. -/
def EvaluationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (T : Distribution G) (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G),
    rightHeckeConvolution μ T h f =
      leftConvolveTest T
        (Hecke.TestFunction.convolution μ (Hecke.HeckeAlgebra.toTestFunction μ h)
          (Hecke.TestFunction.inversion f)) 1

/-- The displayed inclusion chain, with its analogous left inclusion. -/
def InclusionsStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    heckeDistributionSpace μ ≤ compactlySupported ∧
    compactlySupported ≤ essentiallyCompact μ ∧
    essentiallyCompact μ ≤ rightEssentiallyCompact μ ∧
    essentiallyCompact μ ≤ leftEssentiallyCompact μ

/-- Essential compactness strengthens the products from compact support to H(G). -/
def RangePreservationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    (∀ (T : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ),
      rightHeckeConvolution μ (T : Distribution G) h ∈ heckeDistributionSpace μ) ∧
    (∀ (T : leftEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ),
      leftHeckeConvolution μ h (T : Distribution G) ∈ heckeDistributionSpace μ)

def Statements : Prop :=
  KernelStatement.{uG} ∧ CompactCompatibilityStatement.{uG} ∧
    InversionStatement.{uG} ∧ AssociativityStatement.{uG} ∧
    EvaluationStatement.{uG} ∧ InclusionsStatement.{uG} ∧
    RangePreservationStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardFullHecke
