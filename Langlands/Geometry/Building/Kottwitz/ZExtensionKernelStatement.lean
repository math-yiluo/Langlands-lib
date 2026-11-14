import Langlands.Geometry.Building.Kottwitz.ReductiveMap

/-! # KP Proposition 11.5.3: surjectivity on Kottwitz kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Proposition 11.5.3, kernel clause: for every actual z-extension
`1 → Z → H → G → 1`, the image under `p : H → G` of the constructed Kottwitz kernel
of `H` is the constructed Kottwitz kernel of `G`. The first conjunct concerns points
with coefficients in `K = UnramifiedClosure F` of groups defined over any compatible
field of definition `k`; the second concerns `F`-rational points and the rational maps
`reductiveKottwitzRational`. -/
def ZExtensionKottwitzKernelSurjectivityStatement : Prop :=
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (z : ZExtension G),
    (reductiveKottwitz F k z.H z.isZExtension.source_reductive).ker.map
        (z.H.affinePointsTarget z.p (CommAlgCat.of k (UnramifiedClosure F))) =
      (reductiveKottwitz F k G hG).ker) ∧
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (z : ZExtension G),
    (reductiveKottwitzRational F z.H z.isZExtension.source_reductive).ker.map
        (rationalPoints.map z.p) =
      (reductiveKottwitzRational F G hG).ker)

end Langlands.Geometry.Building.Kottwitz
