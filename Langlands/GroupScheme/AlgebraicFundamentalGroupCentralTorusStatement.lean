import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctor
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.ZExtension
import Mathlib.FieldTheory.IsSepClosed

/-! # Exactness of algebraic fundamental groups for a central torus quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AlgebraicFundamentalGroup

/-- KP §11.5 and the proof of Lemma 11.5.1, for an arbitrary central torus:
if `Z` is a closed central torus of `H` and `G` is the fppf quotient of `H` by
the full subgroup functor of `Z`, then `0 → π₁(Z) → π₁(H) → π₁(G) → 0` is
exact for the actual selected maps induced by `i` and `p`. -/
def CentralTorusFundamentalExactnessStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (hZ : IsTorus Z.toGrp)
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
    (i : Z.toGrp ⟶ H) (p : H ⟶ G),
    IsClosedSubgroup i → IsCentral i →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
    Function.Injective
        (fundamentalGroupMap k E Z.toGrp H hZ.isConnectedReductive_of_fieldSplitting hH i) ∧
      Function.Surjective (fundamentalGroupMap k E H G hH hG p) ∧
      LinearMap.range
          (fundamentalGroupMap k E Z.toGrp H hZ.isConnectedReductive_of_fieldSplitting hH i) =
        LinearMap.ker (fundamentalGroupMap k E H G hH hG p)

/-- The induced-torus special case: every z-extension gives the exact sequence
`0 → π₁(Z) → π₁(H) → π₁(G) → 0`, as stated in the proof of KP Lemma 11.5.1. -/
theorem CentralTorusFundamentalExactnessStatement.zExtension
    (h : CentralTorusFundamentalExactnessStatement.{u})
    (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : ZExtension G) :
    Function.Injective
        (fundamentalGroupMap k E z.Z.toGrp z.H
          z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting
          z.isZExtension.source_reductive z.i) ∧
      Function.Surjective
        (fundamentalGroupMap k E z.H G z.isZExtension.source_reductive
          z.isZExtension.target_reductive z.p) ∧
      LinearMap.range
          (fundamentalGroupMap k E z.Z.toGrp z.H
            z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting
            z.isZExtension.source_reductive z.i) =
        LinearMap.ker
          (fundamentalGroupMap k E z.H G z.isZExtension.source_reductive
            z.isZExtension.target_reductive z.p) :=
  h k E z.Z z.isZExtension.induced.isTorus z.H G z.isZExtension.source_reductive
    z.isZExtension.target_reductive z.i z.p z.isZExtension.closed z.isZExtension.central
    z.isZExtension.quotient

end AlgebraicFundamentalGroup

end Langlands.GroupScheme
