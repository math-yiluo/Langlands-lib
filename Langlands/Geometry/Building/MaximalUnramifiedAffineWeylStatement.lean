import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-! # The affine root system and affine Weyl group over the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **AS 3 and the first half of AS 5 over the maximal unramified extension**
(Kaletha–Prasad, Proposition 6.3.13). Let `K = inertiaFixedField F` be the maximal
unramified extension of a nonarchimedean local field `F`, with its normalized integer-valued
valuation, and let `C` be supplied building data for an affine `K`-group `H`. Then the set
`Ψ = C.affineRoots` of affine roots of the apartment is an affine root system (including the
rank-zero case), and every element of its affine Weyl group `W(Ψ)` is the action on the
apartment of a `K`-point of the normalizer `N = N_H(S)` of the maximal split torus. -/
def MaximalUnramifiedAffineWeylStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))) [IsAffineHom H.X.hom]
    (C : MaximalUnramified.BuildingData F H),
    AffineRootSystem.IsAffineRootSystemWithRankZero C.affineRoots ∧
      AffineRootSystem.affineWeylGroup C.affineRoots ≤ C.apartment.normalizerAffineEquiv.range

end Langlands.Geometry.Building
