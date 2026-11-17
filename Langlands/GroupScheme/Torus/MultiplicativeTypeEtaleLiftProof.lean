import Langlands.GroupScheme.HomScheme.MultiplicativeTypeChartCover
import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupSplitting
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableSmooth
import Langlands.Algebra.DiagonalizableHomSmooth
import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupChartCoverReduction

/-! # Multiplicative-type subgroups of a fibre lift to an étale neighbourhood -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Chart covers over affine bases of finite type over `ℤ`.** For every finitely generated
commutative ring `R` and every smooth affine group `G` over `Spec R`, the window charts of the
functor of closed multiplicative-type subgroups of `G` are open charts covering all field
points. -/
theorem MultiplicativeTypeSubgroupModuli.finiteTypeChartCover :
    MultiplicativeTypeSubgroupModuli.FiniteTypeChartCoverStatement.{u} :=
  HomScheme.MultiplicativeTypeChart.finiteTypeChartCover_of
    (fun G _ _ _ _ i hi hL => HomScheme.exists_fppf_diagPoints G i hi hL)
    (fun _ _ G _ _ => HomScheme.FiniteDiagonalizable.smooth_hopfAlgebra G)
    (fun _ _ _ _ _ _ _ _ _ => inferInstance)

/-- **Étale lifting of multiplicative-type subgroups of a fibre** (Conrad 2014, Proposition
3.1.6; SGA 3, Exp. XI, 5.8(a)). -/
theorem multiplicativeTypeEtaleLift : MultiplicativeTypeEtaleLiftStatement.{u} :=
  MultiplicativeTypeSubgroupModuli.multiplicativeTypeEtaleLift_of_finiteTypeCharts
    MultiplicativeTypeSubgroupModuli.finiteTypeChartCover

end Langlands.GroupScheme
