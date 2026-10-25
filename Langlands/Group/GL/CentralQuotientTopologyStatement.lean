import Langlands.Group.GL.PadicBlocks
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Topology and Haar measures on actual GL and Levi central quotients -/

namespace Langlands

universe uG uF

/-- The topology and measure properties needed to compare Haar normalizations
on the quotient by the full group center. -/
def CentralQuotientHaarTopology (G : Type uG) [Group G] [TopologicalSpace G] : Prop :=
  let Q := G ⧸ Subgroup.center G
  IsTopologicalGroup Q ∧ T2Space Q ∧ LocallyCompactSpace Q ∧
    SecondCountableTopology Q ∧
    ∀ [MeasurableSpace Q] [BorelSpace Q],
      (∃ μ : MeasureTheory.Measure Q, μ.IsHaarMeasure) ∧
      ∀ (μ : MeasureTheory.Measure Q) [μ.IsHaarMeasure], MeasureTheory.SigmaFinite μ

/-- Every actual general linear group and product Levi has a locally compact,
Hausdorff, second-countable full central quotient, with sigma-finite Haar
measures for every Borel realization. -/
def GLBlockCentralQuotientTopologyStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ),
      CentralQuotientHaarTopology (GeneralLinear n F.Carrier) ∧
      ∀ B : GeneralLinear.BlockShape n,
        letI := T.leviTopology B
        CentralQuotientHaarTopology (B.Levi F.Carrier)

end Langlands
