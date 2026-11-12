import Langlands.Representation.Aubert.General.RationalRankOneGeometricFiltrationAssembly
import Langlands.Representation.Aubert.General.RationalGeometricObjectFiltrationConstruction
import Langlands.Representation.Aubert.General.RationalGeometricEpsilonBalance

/-! # The rank-one geometric Jacquet computation on actual rational points -/

noncomputable section

set_option maxHeartbeats 1600000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The actual maximal-source geometric filtration exists, with its specified
closed identity orbit at the quotient end of every self composite. -/
theorem rationalMaximalSourceGeometricFiltration :
    RationalMaximalSourceGeometricFiltrationStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent _hMin _hAssoc J _hJ σ I _hI
  refine ⟨pointGeometricObjectFiltrationOfEpsilonBalance
    i ν hG hi hν hStandard hN hZ actual hIdent hM hU hInter hLength hSimple I J ?_ σ⟩
  intro w _hw n _hn
  exact geometricEpsilon_mul_eq_one i ν hStandard hG hi hν hN hRoots I J
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
    n hU (isClosed_standard_parabolic i ν hStandard hG hi hν) hM
    (continuous_standard_projection i ν hStandard hG hi hν I)
    (continuous_standard_projection i ν hStandard hG hi hν J)

/-- The complete rank-one object-level geometric Jacquet computation, with
no parameters outside the published proposition. -/
theorem rationalRankOneGeometricJacquet :
    RationalRankOneGeometricJacquetStatement.{u, v} :=
  rationalRankOneGeometricJacquetOfMaximalSourceFiltration
    rationalMaximalSourceGeometricFiltration

end Langlands.Aubert.General.RationalPointFamily
