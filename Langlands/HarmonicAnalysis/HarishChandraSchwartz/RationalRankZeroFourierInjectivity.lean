import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierReconstruction

/-! # Fourier injectivity in relative semisimple rank zero -/

universe u uV

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard.FourierInversion

/-- The rank-zero case of the zero-Fourier implication in Waldspurger VIII.5,
with all data of the actual local Fourier transform. -/
def RationalRankZeroFourierInjectivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    relativeRootRank i = 0 → RationalLocalFourierInjectivityStatement.{u, uV} G

end Langlands.HarishChandraSchwartz
