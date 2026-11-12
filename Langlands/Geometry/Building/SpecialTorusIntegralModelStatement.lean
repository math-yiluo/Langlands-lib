import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement

/-! # The integral model behind special tori (building input of KP Proposition 9.3.4) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **A smooth model adapted to a maximal split torus** (the building input of KP
Proposition 9.3.4). Let `F` be a nonarchimedean local field with integers `𝒪[F]` and residue
field `𝓀[F]`, and let `O_K` be the integers of its maximal unramified extension `K`. For every
maximal `F`-split torus `S` of a connected reductive `F`-group `G` there is a smooth affine
`𝒪[F]`-model `M` of `G` with connected special fibre such that

* `M` contains a closed split `𝒪[F]`-torus whose generic fibre is `S`, and
* the base change of `M` to `O_K` contains a closed split `O_K`-torus whose generic fibre is
  a maximal `K`-split torus of `G_K`. -/
def SpecialTorusIntegralModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
      IsMaximalSplitTorus iS →
      ∃ M : IntegralModel ↥𝒪[F] F G, M.IsSmooth ∧
        ConnectedSpace
          ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group).X.left ∧
        (∃ (𝒮 : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))) (j : 𝒮.toGrp ⟶ M.group)
            (e : (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj 𝒮 ≅ S),
          IsSplitTorus 𝒮.toGrp ∧ IsClosedSubgroup j ∧
            M.genericTorusMap 𝒮 j = CommGroupScheme.groupHom e.hom ≫ iS) ∧
        ∃ (𝒜 : CommGroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F))))
          (a : 𝒜.toGrp ⟶ M.baseChangeUnramified.group),
          IsSplitTorus 𝒜.toGrp ∧ IsClosedSubgroup a ∧
            IsMaximalSplitTorus (M.baseChangeUnramified.genericTorusMap 𝒜 a)

end Langlands.Geometry.Building
