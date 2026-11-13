import Langlands.Geometry.Building.Kottwitz.ReductiveMap

/-! # KP Proposition 11.5.4: the zero subgroup is the Kottwitz kernel -/

universe u
open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

/-- The Library's `G(F)^0`, for every defining datum, is exactly the actual Kottwitz kernel. -/
def ZeroKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (Z : GroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G) (j : Z ⟶ G)
    (d : ZeroSubgroupDatum i j),
    d.zeroSubgroup = (reductiveKottwitzRational F G hG).ker

end Langlands.Geometry.Building.Kottwitz
