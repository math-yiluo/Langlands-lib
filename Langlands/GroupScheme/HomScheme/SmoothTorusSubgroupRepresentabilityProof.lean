import Langlands.GroupScheme.HomScheme.TorusChartCover
import Langlands.GroupScheme.HomScheme.TorusSubgroupSplitting
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableSmooth
import Langlands.Algebra.DiagonalizableHomSmooth
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartCoverReductionProof
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartGluingProof

/-! # Smooth moduli of actual closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- **Chart covers over affine bases of finite type over `ℤ`.** -/
theorem finiteTypeChartCover : FiniteTypeChartCoverStatement.{u} :=
  HomScheme.TorusChart.finiteTypeChartCover_of
    (fun G _ _ _ _ i hi hL => HomScheme.exists_etale_splitPoints G i hi hL)
    (fun _ _ G _ _ => HomScheme.FiniteDiagonalizable.smooth_hopfAlgebra G)
    (fun _ _ _ _ _ _ _ _ _ _ => inferInstance)

/-- **Smooth moduli of actual closed torus subgroups.** A smooth affine group scheme over any
base scheme has a smooth parameter scheme carrying a universal family of closed relative-torus
subgroups. -/
theorem smoothTorusSubgroupRepresentability : SmoothTorusSubgroupRepresentabilityStatement.{u} :=
  chartGluing (chartCoverReduction finiteTypeChartCover)

end Langlands.GroupScheme.TorusSubgroupModuli
