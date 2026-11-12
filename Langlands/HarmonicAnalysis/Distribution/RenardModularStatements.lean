import Langlands.HarmonicAnalysis.Distribution.Haar
import Mathlib.GroupTheory.Index

/-! # Renard II.3.7–II.3.8: modular formulas on actual distributions -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis.Distribution.RenardModular

universe uG

/-- The distribution character and the displayed two-sided translation integral. -/
def TranslationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    (∀ g : G, GroupAction.rightDistributions g (ofMeasure μ) =
      ((renardModular g : ℝ) : ℂ) • ofMeasure μ) ∧
    ∀ (f : SchwartzBruhat G) (h h' : G),
      (∫ x, f (h' * x * h⁻¹) ∂μ) =
        ((renardModular h : ℝ) : ℂ) * ofMeasure μ f

/-- Positivity, local constancy, continuity and compact-subgroup triviality in
Renard's reciprocal convention. -/
def RegularityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    (∀ g : G, 0 < renardModular g) ∧
      IsLocallyConstant (renardModular (G := G)) ∧
      Continuous (renardModular (G := G)) ∧
      ∀ (K : Subgroup G), IsCompact (K : Set G) →
        ∀ g ∈ K, renardModular g = 1

/-- The inverse modular density is the inverted left Haar distribution and is
right invariant, without second countability. -/
def InversionDensityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∃ d : LocallyConstant G ℂ,
      (∀ g, d g = (((renardModular g : ℝ)⁻¹) : ℂ)) ∧
      IsRightInvariant (density μ d) ∧
      GroupAction.inversionDistributions (ofMeasure μ) = density μ d

/-- The source definition of unimodularity, its distribution meaning and its
three examples. -/
def UnimodularityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ((∀ g : G, renardModular g = 1) ↔ IsRightInvariant (ofMeasure μ)) ∧
      ((∀ g h : G, g * h = h * g) → ∀ g : G, renardModular g = 1) ∧
      (IsCompact (Set.univ : Set G) → ∀ g : G, renardModular g = 1) ∧
      ((∀ g : G, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ g ∈ K) →
        ∀ g : G, renardModular g = 1)

/-- Automorphism scaling and the integral formula (II.3.7.1). -/
def AutomorphismStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (σ : G ≃ₜ* G),
    GroupAction.continuousAutomorphismDistributions σ (ofMeasure μ) =
      ((renardAutomorphismModule σ : ℝ) : ℂ) • ofMeasure μ ∧
    ∀ f : SchwartzBruhat G, (∫ x, f (σ x) ∂μ) =
      ((renardAutomorphismModule σ : ℝ) : ℂ) * ofMeasure μ f

/-- The automorphism module of actual inner conjugation. -/
def InnerAutomorphismStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (h : G) (σ : G ≃ₜ* G),
    (∀ x, σ x = h * x * h⁻¹) →
      renardAutomorphismModule σ = renardModular h

/-- The exact preimage-oriented mass identities and index quotient (II.3.8.1). -/
def IndexFormulaStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (σ : G ≃ₜ* G) (K : OpenSubgroup G), IsCompact (K : Set G) →
    let P := K.toSubgroup.comap σ.toMonoidHom
    let L := K.toSubgroup ⊓ P
    μ (σ ⁻¹' (K : Set G)) =
      (renardAutomorphismModule σ : ℝ≥0∞) * μ (K : Set G) ∧
    μ (K : Set G) = (L.relIndex K.toSubgroup : ℝ≥0∞) * μ (L : Set G) ∧
    μ (P : Set G) = (L.relIndex P : ℝ≥0∞) * μ (L : Set G) ∧
    renardAutomorphismModule σ =
      (L.relIndex P : ℝ≥0) / (L.relIndex K.toSubgroup : ℝ≥0)

def Statements : Prop :=
  TranslationStatement.{uG} ∧ RegularityStatement.{uG} ∧
    InversionDensityStatement.{uG} ∧ UnimodularityStatement.{uG} ∧
    AutomorphismStatement.{uG} ∧ InnerAutomorphismStatement.{uG} ∧
    IndexFormulaStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardModular
