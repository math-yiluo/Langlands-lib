import Langlands.Geometry.Building.KPLieFiltrationDual
import Langlands.Geometry.Building.KPNilpotentCoset

/-!
# KP Proposition 13.7.4 (1) on supplied Lie filtrations

Let `X ∈ 𝔤_{x,r}`. If the translate `Ξ = X + 𝔤_{x,r+}` in the Lie algebra meets `𝔤_{y,s}` for
some point `y` of the apartment and some `s > r`, then `Ξ` contains a nilpotent element. The
lattices are those of supplied Lie filtration data, extended to real depths.

When the real filtration at `x` is decreasing, in particular under `IsPeriodic`, `𝔤_{x,r+}` lies in
`𝔤_{x,r}` (`lieFiltrationPlusReal_le`) and `Ξ` is KP's coset in `𝔤_{x,r}/𝔤_{x,r+}`. For arbitrary
supplied data `𝔤_{x,r+}` need not lie in `𝔤_{x,r}`; the statement then concerns the translate in
the ambient Lie algebra, with `X` a representative taken from `𝔤_{x,r}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP Proposition 13.7.4 (1) for supplied Lie filtration data and points of the apartment.
Let `L` supply the lattices `z_r` and `u_ψ`, let `x, y` be points of the apartment, and let
`r < s` be real numbers. If `X ∈ 𝔤_{x,r}` and the translate `X + 𝔤_{x,r+}` in the Lie algebra
meets `𝔤_{y,s}`, then the translate contains an element contracted to `0` by a 1-parameter
subgroup of `G` over `F`. Under `IsPeriodic` the translate is a coset in `𝔤_{x,r}/𝔤_{x,r+}`; for
arbitrary `L`, `𝔤_{x,r+}` need not lie in `𝔤_{x,r}`. -/
def DegenerateCosetOfDeeperIntersectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (L : P.LieFiltrationData)
    (x y : P.Apartment) (r s : ℝ), r < s →
    ∀ X ∈ L.lieFiltrationReal x r,
      (∃ Y ∈ L.lieFiltrationReal y s, Y - X ∈ L.lieFiltrationPlusReal x r) →
        IsDegenerateLieCoset (L.lieFiltrationPlusReal x r) X

end Langlands.Geometry.Building
