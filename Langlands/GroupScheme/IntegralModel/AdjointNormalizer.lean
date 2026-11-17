import Langlands.GroupScheme.Adjoint.CompactNormalizer
import Langlands.GroupScheme.IntegralModel.MaximalCompact
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints
import Langlands.GroupScheme.IntegralModel.LocalIntegralSeparation
import Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerReduction
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Integral models and normalizers of dense integral images in adjoint groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

namespace IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G A : GroupScheme (Spec (CommRingCat.of F))}

/-- The integral points of the target model normalize the image of the source integral
points under the supplied generic homomorphism. -/
def IntegralPointsNormalizeImage
    (M : IntegralModel ↥𝒪[F] F G) (N : IntegralModel ↥𝒪[F] F A) (q : G ⟶ A) : Prop :=
  N.integralPoints ≤
    Subgroup.normalizer (M.integralPoints.map (rationalPoints.map q) : Set (rationalPoints A))

/-- In an adjoint generic group with a reductive-special-fibre model, a dominant image of
integral points has precisely the target integral points as normalizer, provided those
target integral points normalize the image. -/
theorem normalizer_map_integralPoints_eq
    (hG : IsConnectedReductive G) (hA : IsAdjoint A)
    (M : IntegralModel ↥𝒪[F] F G) (N : IntegralModel ↥𝒪[F] F A)
    (hN : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj N.group))
    (q : G ⟶ A) [IsDominant q.hom.hom.left]
    (hnorm : M.IntegralPointsNormalizeImage N q) :
    Subgroup.normalizer (M.integralPoints.map (rationalPoints.map q) :
      Set (rationalPoints A)) = N.integralPoints := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let hAr := hA.isSemisimple.isConnectedReductive
  let : IsAffineHom A.X.hom := hAr.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : Smooth A.X.hom := hAr.smooth
  let : TopologicalSpace (rationalPoints A) := rationalPointTopology F A.X
  let : IsTopologicalGroup (rationalPoints A) := rationalPoint_isTopologicalGroup F A
  have hMd := Langlands.BruhatTits.RationalPoints.hasDenseRationalPointFamily_subgroup_of_isOpen
    F G M.integralPoints M.isOpen_integralPoints_localField
  have hMb := isAlgebraicallyBounded_of_isCompact M.isCompact_integralPoints_localField
  have hQb : IsAlgebraicallyBounded F A.X
      (M.integralPoints.map (rationalPoints.map q) : Set (rationalPoints A)) :=
    hMb.image q.hom.hom
  have hQd := SubgroupFunctor.hasDenseRationalPointFamily_map q M.integralPoints hMd
  have hc := isCompact_closure_normalizer_of_adjoint F A hA
    (M.integralPoints.map (rationalPoints.map q)) hQb hQd
  have hmax := maximalCompactStatement F A hAr N hN
  have heq := hmax.2
    (Subgroup.normalizer (M.integralPoints.map (rationalPoints.map q) :
      Set (rationalPoints A))).topologicalClosure
    hc (hnorm.trans (Subgroup.le_topologicalClosure _))
  exact le_antisymm ((Subgroup.le_topologicalClosure _).trans heq.le) hnorm

end IntegralModel

end Langlands.GroupScheme
