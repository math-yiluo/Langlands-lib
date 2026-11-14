import Langlands.Geometry.Building.Kottwitz.CocenterZeroReduction
import Langlands.Geometry.Building.Kottwitz.TorusKernelStatement
import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement

/-! # The Kottwitz kernel for a simply-connected-derived group -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

/-- The torus kernel equality and the cocenter specification identify the zero
subgroup with the simply-connected-derived Kottwitz kernel on coefficient points. -/
theorem simplyConnectedZeroKernel_of_torus
    (htorus : TorusKottwitzKernelStatement.{u})
    (hmap : SimplyConnectedDerivedKottwitzStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)]
    [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (hsc : HasSimplyConnectedDerivedGroup G)
    (E : UnramifiedZeroDatum F (baseChanged k (UnramifiedClosure F) G)) :
    E.zeroPoints = (simplyConnectedDerivedKottwitz F k G hG hsc).ker.comap
      (baseChangeCoeffEquiv k (UnramifiedClosure F) G).toMonoidHom := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨c⟩ := nonempty_cocenter k G hG
  let Q := (CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj c.torus
  let q := (GroupScheme.baseChange (baseMap k (UnramifiedClosure F))).map c.quotient
  have hQ : IsTorus Q.toGrp := c.isTorus.baseChange
  let : IsAffine Q.X.left := torusIsAffine (UnramifiedClosure F) Q hQ
  have hq := c.baseChange_isQuotient (K := UnramifiedClosure F)
  have hscK := hasSimplyConnectedDerivedGroup_baseChange
    (K := UnramifiedClosure F) hsc
  have hzero := zeroPoints_eq_cocenter_comap E hscK Q hQ q hq
  have hsplit := (cocenter_torusNormIwahori_image E Q hQ q hq).1
  have htorusKernel := htorus F k c.torus c.isTorus E.L hsplit
  have hlaw : CocenterKottwitzLawAt F k G hG c
      (simplyConnectedDerivedKottwitz F k G hG hsc) :=
    (hmap F k G hG hsc).2.1 c
  have hinj : Function.Injective (cocenterTargetMap F k G hG c) :=
    ((hmap F k G hG hsc).2.2.2 c).1.1
  rw [hzero, htorusKernel]
  ext x
  change torusKottwitz F k c.torus c.isTorus
      (baseChangeCoeffEquiv k (UnramifiedClosure F) c.torus.toGrp
        (rationalPoints.map q x)) = 1 ↔
    simplyConnectedDerivedKottwitz F k G hG hsc
      (baseChangeCoeffEquiv k (UnramifiedClosure F) G x) = 1
  rw [baseChangeCoeffEquiv_map]
  have hsquare := hlaw (baseChangeCoeffEquiv k (UnramifiedClosure F) G x)
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    apply hinj
    simp only [hsquare, hx, toAdd_one, map_zero]
  · intro hx
    apply Multiplicative.toAdd.injective
    simpa only [hx, toAdd_one, map_zero] using hsquare.symm

end Langlands.Geometry.Building.Kottwitz
