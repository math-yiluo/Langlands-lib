import Langlands.GroupScheme.Rational.FiniteFieldSplitUnipotentProductStatement
import Langlands.GroupScheme.Rational.SplitUnipotentProductGeometric
import Langlands.GroupScheme.Rational.SplitUnipotentProductPointCount
import Langlands.GroupScheme.Rational.SplitUnipotentProductBaseChange
import Langlands.GroupScheme.Rational.SubgroupIntersectionBaseChangeProperties
import Langlands.GroupScheme.Rational.SplitSeriesBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

theorem finiteFieldSplitUnipotentProduct :
    FiniteFieldSplitUnipotentProductStatement.{u} := by
  intro k _ _ U V C _ _ _ _ _ _ _ _ _ j c _hj hc hU hV hC hEs hEc hE hsurj
  let E := subgroupIntersection j c
  let : Smooth E.X.hom := hEs
  let : ConnectedSpace E.X.left := hEc
  let : IsAffineHom E.X.hom := isAffineHom_subgroupIntersection j c hc
  have hdim : Lie.dimension V + Lie.dimension C = Lie.dimension U + Lie.dimension E :=
    lieDimension_add_intersection_of_rationalPoints_mul_surjective j c hV hC hU hE hsurj
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let F := GroupScheme.baseChange b
  let VK := F.obj V
  let CK := F.obj C
  let UK := F.obj U
  let jK : VK ⟶ UK := F.map j
  let cK : CK ⟶ UK := F.map c
  let EK := subgroupIntersection jK cK
  let : Smooth VK.X.hom := by
    change Smooth (pullback.snd V.X.hom b)
    infer_instance
  let : Smooth CK.X.hom := by
    change Smooth (pullback.snd C.X.hom b)
    infer_instance
  let : Smooth UK.X.hom := by
    change Smooth (pullback.snd U.X.hom b)
    infer_instance
  let : IsAffineHom VK.X.hom := by
    change IsAffineHom (pullback.snd V.X.hom b)
    infer_instance
  let : IsAffineHom CK.X.hom := by
    change IsAffineHom (pullback.snd C.X.hom b)
    infer_instance
  let : IsAffineHom UK.X.hom := by
    change IsAffineHom (pullback.snd U.X.hom b)
    infer_instance
  let : ConnectedSpace VK.X.left := V.connectedSpace_baseChange_of_smooth_affine b
  let : ConnectedSpace CK.X.left := C.connectedSpace_baseChange_of_smooth_affine b
  let : ConnectedSpace UK.X.left := U.connectedSpace_baseChange_of_smooth_affine b
  have hcK : IsClosedSubgroup cK := hc.baseChange b
  let : IsAffineHom EK.X.hom := isAffineHom_subgroupIntersection jK cK hcK
  let : Smooth EK.X.hom := smooth_subgroupIntersection_baseChange b j c
  let : IsAffineHom (F.obj E).X.hom := by
    change IsAffineHom (pullback.snd E.X.hom b)
    infer_instance
  have hVdim : Lie.dimension VK = Lie.dimension V :=
    SubgroupProductOrbit.lie_dimension_baseChange V b
  have hCdim : Lie.dimension CK = Lie.dimension C :=
    SubgroupProductOrbit.lie_dimension_baseChange C b
  have hUdim : Lie.dimension UK = Lie.dimension U :=
    SubgroupProductOrbit.lie_dimension_baseChange U b
  have hEdim : Lie.dimension EK = Lie.dimension E := by
    calc
      _ = Lie.dimension (F.obj E) :=
        (Lie.dimension_eq_of_iso (subgroupIntersectionBaseChangeIso b j c)).symm
      _ = _ := SubgroupProductOrbit.lie_dimension_baseChange E b
  have hVK : IsSplitUnipotent VK := hV.baseChange K
  have hCK : IsSplitUnipotent CK := hC.baseChange K
  obtain ⟨hsm, hs⟩ := ProductGeometry.smooth_surjective_subgroupMultiplication_of_lie_dimension
    jK cK hcK hVK.isUnipotent hCK.isUnipotent (inferInstance : Smooth EK.X.hom)
    (by
      change Lie.dimension VK + Lie.dimension CK = Lie.dimension EK + Lie.dimension UK
      omega)
  exact smooth_surjective_subgroupMultiplication_of_fieldExtension
    (K := K) j c hsm hs

end Langlands.GroupScheme.RelativeRoot
