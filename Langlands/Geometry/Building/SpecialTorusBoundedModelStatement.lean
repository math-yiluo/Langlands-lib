import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # A smooth model containing the bounded points of two split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **A smooth model containing the bounded points of two split tori** (the building input of
KP Proposition 9.3.4, before the passage to split tori of the model). Let `F` be a
nonarchimedean local field with integers `𝒪[F]`, let `K` be its maximal unramified extension
with integers `O_K` and normalized valuation `v_K`, and let `G` be a connected reductive
`F`-group with a maximal `F`-split torus `S`. Then there is a smooth affine `𝒪[F]`-model `M`
of `G` such that, in `G(K)`,

* the maximal bounded subgroup `S(K)^1 = {s | v_K(χ(s)) = 1 for all χ}` of `S(K)` lies in
  the integral points of the base change of `M` to `O_K`, and
* there is a maximal `K`-split torus `A` of `G_K` whose maximal bounded subgroup `A(K)^1`
  lies in those integral points as well. -/
def SpecialTorusBoundedModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
      IsMaximalSplitTorus iS →
      ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
        (characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (inertiaFixedField F) S.toGrp)).map
            (rationalPoints.map
              ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS)) ≤
          M.baseChangeUnramified.integralPoints ∧
        ∃ (A : CommGroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
          (iA : A.toGrp ⟶ baseChanged F (inertiaFixedField F) G),
          IsMaximalSplitTorus iA ∧
            (characterValuationKernel (MaximalUnramified.valuation F) A.toGrp).map
                (rationalPoints.map iA) ≤
              M.baseChangeUnramified.integralPoints

end Langlands.Geometry.Building
