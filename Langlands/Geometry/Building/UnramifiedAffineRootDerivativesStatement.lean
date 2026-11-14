import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # The derivative root system of the affine roots over the maximal unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- KP Proposition 6.3.13 (derivative part) over `K = inertiaFixedField F`: for every
supplied building datum of an affine `K`-group, the set of derivatives of the affine roots
`Ψ` is the whole relative root system `Φ`, multipliable roots included. -/
def UnramifiedAffineRootDerivativesStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom H.X.hom]
    (C : MaximalUnramified.BuildingData F H),
    AffineRootSystem.derivativeRoots C.affineRoots = Set.range (rootForm C.i)

end Langlands.Geometry.Building
