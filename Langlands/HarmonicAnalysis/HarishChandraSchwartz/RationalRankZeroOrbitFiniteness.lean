import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLocalOrbitFiniteness
import Langlands.GroupScheme.Rational.RelativeRank

/-! # Waldspurger VIII.1.2 in relative semisimple rank zero -/

universe u uV

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

/-- The local orbit-finiteness assertion on an actual connected reductive group
whose maximal split torus has relative-root-span rank zero. -/
def RationalRankZeroDiscreteSeriesOrbitFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    relativeRootRank i = 0 → RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} G

end Langlands.HarishChandraSchwartz
