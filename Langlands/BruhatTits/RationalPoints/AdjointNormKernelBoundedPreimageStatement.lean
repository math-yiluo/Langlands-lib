import Langlands.BruhatTits.RationalPoints.BoundedSetOperations
import Langlands.GroupScheme.Adjoint.Quotient

/-! # Bounded adjoint preimages inside the rational norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.RationalPoints

/-- The preimage of an algebraically bounded set in an actual adjoint
quotient is algebraically bounded after intersection with the common kernel
of all actual rational-character norms. -/
def AdjointNormKernelBoundedPreimageStatement : Prop :=
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
    ∀ B : Set (rationalPoints A),
      IsAlgebraicallyBounded F A.X B →
      IsAlgebraicallyBounded F G.X
        ((rationalPoints.map q ⁻¹' B) ∩
          (Langlands.Plancherel.rationalCommonNormKernel G : Set (rationalPoints G)))

end Langlands.BruhatTits.RationalPoints
