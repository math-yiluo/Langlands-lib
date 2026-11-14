import Langlands.Geometry.Building.Kottwitz.TorusMap
import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Torus.BaseChange

/-! # KP Proposition 11.1.5: the torus zero subgroup is the Kottwitz kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Proposition 11.1.5, `T(K)^0 = ker(κ_T)`. Here `T(K)^0` is the norm image of the bounded
subgroup for every finite Galois splitting field `L/K`, and `κ_T` is the constructed map on
`K`-coefficient points. Both are compared on the rational points of `T_K`. -/
def TorusKottwitzKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [Normal k (UnramifiedClosure F)]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp),
    let TK := (CommGroupScheme.baseChange (baseMap k (UnramifiedClosure F))).obj T;
    letI : IsAffine TK.X.left := torusIsAffine (UnramifiedClosure F) TK hT.baseChange;
    ∀ (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
      [FiniteDimensional (UnramifiedClosure F) L] [IsGalois (UnramifiedClosure F) L],
      IsSplitTorus (baseChanged (UnramifiedClosure F) L TK.toGrp) →
      torusNormIwahori (UnramifiedClosure F) L (intermediateValuation F L) TK =
        (torusKottwitz F k T hT).ker.comap
          (baseChangeCoeffEquiv k (UnramifiedClosure F) T.toGrp).toMonoidHom

end Langlands.Geometry.Building.Kottwitz
