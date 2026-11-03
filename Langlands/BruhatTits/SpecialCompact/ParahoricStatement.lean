import Langlands.Geometry.Building.KPParahoric
import Langlands.Geometry.Building.SpecialCompact

/-!
# The parahoric subgroup of an apartment point lies in its compact stabilizer

`P_x = G(F)^0_x = Z(F)^0 · G(F)^♯_x ⊆ K_x = G(F)^1 ∩ G(F)_x` for every point `x` of the
apartment (KP Definition 7.4.1(4), Definition 2.6.30 and Proposition 7.6.4(1)). At a special
vertex `x` the right side is the special compact subgroup `K_0`. The inclusion can be strict.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- For every nonarchimedean local field `F`, every `F`-group `G`, all parahoric building data
`P` for `G` (connected reductive `G`, maximal split torus `S`, an `N(F)`-stable class `A(S)` of
valuations satisfying V 6 on `Z(F)`, and the data of KP Definition 2.6.23 for `Z(F)^0` and
`G(F)^0` relative to the same `S` and `Z = Z_G(S)`) and every point `x` of the apartment, the
parahoric subgroup `P_x = Z(F)^0 · G(F)^♯_x` lies in
`K_x = G(F)^1 ∩ G(F)_x = P.apartment.specialCompactSubgroup x`. -/
def ParahoricLeCompactStabilizer : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (x : P.Apartment),
      P.parahoricAt x ≤ P.apartment.specialCompactSubgroup x

end Langlands.BruhatTits.SpecialCompact
