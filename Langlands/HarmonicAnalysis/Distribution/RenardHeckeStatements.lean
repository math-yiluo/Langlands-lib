import Langlands.HarmonicAnalysis.Distribution.CompactSubgroup
import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.Distribution.HeckeRealization
import Langlands.HarmonicAnalysis.GroupFunctionSpaces
import Langlands.Representation.Hecke.DoubleCosetSandwich
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Renard II.3.12: distribution realization of compact-open Hecke corners -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardHecke

universe uG

/-- The existing Hecke carrier realizes precisely the existing test-density
range in the original algebraic dual. -/
def DensityRealizationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    Function.Injective (heckeDistribution μ) ∧
      heckeDistributionSpace μ = LinearMap.range (testDensity μ)

/-- The actual compact-open density agrees with normalized subgroup Haar. -/
def NormalizedIndicatorStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    heckeDistribution μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) =
      (compactSubgroupHaar K.toSubgroup hK : Distribution G)

/-- Finite families of Hecke distributions have actual compact-open two-sided
local units, and the subgroup may refine a prescribed open subgroup. -/
def LocalUnitsStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (s : Finset (compactlySupported (X := G))) (U : OpenSubgroup G),
    (∀ T ∈ s, (T : Distribution G) ∈ heckeDistributionSpace μ) →
    ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), K ≤ U ∧
      ∀ T ∈ s,
        convolution (compactSubgroupHaar K.toSubgroup hK) T = T ∧
        convolution T (compactSubgroupHaar K.toSubgroup hK) = T

/-- The exact reverse-subgroup criterion for the two-sided idempotent order. -/
def IdempotentOrderStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K L : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hL : IsCompact (L : Set G)),
    (convolution (compactSubgroupHaar K.toSubgroup hK)
        (compactSubgroupHaar L.toSubgroup hL) = compactSubgroupHaar K.toSubgroup hK ∧
      convolution (compactSubgroupHaar L.toSubgroup hL)
        (compactSubgroupHaar K.toSubgroup hK) = compactSubgroupHaar K.toSubgroup hK) ↔
      L ≤ K

/-- Inversion reverses compact convolution and fixes the compact-open
idempotents. The inverse factors are required to be the actual inversions. -/
def InversionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    (∀ T S : compactlySupported (X := G),
      ∃ Ti Si : compactlySupported (X := G),
        (Ti : Distribution G) = GroupAction.inversionDistributions (T : Distribution G) ∧
        (Si : Distribution G) = GroupAction.inversionDistributions (S : Distribution G) ∧
        GroupAction.inversionDistributions (convolution T S : Distribution G) =
          (convolution Si Ti : Distribution G)) ∧
    ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
      GroupAction.inversionDistributions
        (compactSubgroupHaar K.toSubgroup hK : Distribution G) =
          (compactSubgroupHaar K.toSubgroup hK : Distribution G)

/-- The already constructed unital corner realizes exactly the compact
bi-K-invariant distribution subspace, and its unit realizes e_K. -/
def CornerStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    Set.range (fun h : Hecke.HeckeAlgebra.Corner μ K hK =>
      heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK h)) =
        (GroupFunctionSpaces.compactDistributionsBoth K.toSubgroup : Set (Distribution G)) ∧
    heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK 1) =
      (compactSubgroupHaar K.toSubgroup hK : Distribution G)

/-- The existing mass-one double-coset function is exactly e_K*δ_g*e_K.
Every system of double-coset representatives gives the stated basis. -/
def DoubleCosetBasisStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    (∀ g : G,
      heckeDistribution μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK
        (Hecke.HeckeAlgebra.Corner.massIndicator K hK μ g)) =
        (convolution (convolution (compactSubgroupHaar K.toSubgroup hK) (compactDirac g))
          (compactSubgroupHaar K.toSubgroup hK) : Distribution G)) ∧
    ∀ (ι : Type uG) (r : ι → G),
      (∀ g : G, ∃! i : ι, g ∈ Hecke.TestFunction.doubleCosetSet K (r i)) →
      ∃ b : Module.Basis ι ℂ (GroupFunctionSpaces.compactDistributionsBoth K.toSubgroup),
        ∀ i : ι, (b i : Distribution G) =
          (convolution (convolution (compactSubgroupHaar K.toSubgroup hK)
            (compactDirac (r i))) (compactSubgroupHaar K.toSubgroup hK) : Distribution G)

def Statements : Prop :=
  DensityRealizationStatement.{uG} ∧ NormalizedIndicatorStatement.{uG} ∧
    LocalUnitsStatement.{uG} ∧ IdempotentOrderStatement.{uG} ∧
    InversionStatement.{uG} ∧ CornerStatement.{uG} ∧ DoubleCosetBasisStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardHecke
