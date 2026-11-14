import Langlands.BruhatTits.RationalPoints.BoundedSetOperations
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.AlgebraicGeometry.PointTopology.DenseRationalFamily

/-! # Adjoint images of normalizers of dense bounded subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

/-- A bounded subgroup whose actual rational points are Zariski dense has a
bounded normalizer image in the actual adjoint quotient. -/
def DenseBoundedNormalizerAdjointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (A : GroupScheme (Spec (CommRingCat.of F))) (q : G ⟶ A)
    (hq : IsAdjointQuotient q),
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI : IsAffineHom A.X.hom :=
      hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
    haveI : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
    ∀ H : Subgroup (rationalPoints G),
      IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)) →
      HasDenseRationalPointFamily H.subtype →
      IsAlgebraicallyBounded F A.X
        (rationalPoints.map q ''
          (Subgroup.normalizer (H : Set (rationalPoints G)) : Set (rationalPoints G)))

end Langlands.BruhatTits.RationalPoints
