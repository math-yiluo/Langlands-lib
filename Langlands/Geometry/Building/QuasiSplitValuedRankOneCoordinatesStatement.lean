import Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates

/-! # Existence of coherent valued rank-one coordinates over the maximal unramified field -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- For every indivisible root of supplied building data over the actual maximal
unramified field with torus centralizer, coherent valued SL2 or SU3 coordinates exist,
as determined by whether its double is a relative root. -/
def QuasiSplitValuedRankOneCoordinatesStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffineHom H.X.hom]
    (B : MaximalUnramified.BuildingData F H) (hZ : IsTorus B.centralizer.Z)
    (b : characterLattice B.S),
    b ∈ RelativeRoot.indivisibleRoots B.i →
      (2 • b ∉ relativeRoots B.i → Nonempty (ValuedSL2RootCoordinates B hZ b)) ∧
      (2 • b ∈ relativeRoots B.i → Nonempty (ValuedSU3RootCoordinates B hZ b))

end Langlands.Geometry.Building
