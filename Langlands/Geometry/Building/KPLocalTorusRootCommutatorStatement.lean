import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.FilteredRootProducts

/-! # Positive-depth torus points move root-group filtrations over `K = F^ur`

For quasi-split building data `B` over the maximal unramified extension `K = F^ur` whose
centralizer `Z = Z_G(S)` is a torus (binder `hZ : IsTorus B.centralizer.Z`, with `Z` written
as the commutative group scheme `B.centralizerTorus hZ`), a point `t ∈ Z(K)` with
`r ≤ ω(χ(t) - 1)` for every character `χ` of `Z` over `Ω = F^sep`, at depth `r > 0`, moves
`U_{a,x,s}` by commutators in the block `U_{a,x,r+s} · U_{2a,x,r+s}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

/-- Positive-depth torus action on the root-group filtrations of quasi-split building data
over `K = F^ur`: for `0 < r`, `t ∈ Z(K)` congruent to `1` at depth `r` under every geometric
character of `Z`, `z = j(t)` and `u ∈ U_{a,x,s}`, the commutator `z u z⁻¹ u⁻¹` lies in the
block `U_{a,x,r+s} · U_{2a,x,r+s}` (KP Definition 7.3.3(1) at the constant function `r + s`). -/
def KPLocalTorusRootCommutatorStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)
    (x : B.Apartment) (a : relativeRoots B.i) (r s : ℝ≥0), 0 < r →
    ∀ t ∈ localGeometricCharacterCongruence F (B.centralizerTorus hZ) r,
      ∀ u ∈ B.filtration x a.1 s,
        rationalPoints.map B.centralizer.j t * u *
            (rationalPoints.map B.centralizer.j t)⁻¹ * u⁻¹ ∈
          B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a.1

end Langlands.Geometry.Building
