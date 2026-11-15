import Langlands.Geometry.Building.Kottwitz.FundamentalGroup
import Langlands.GroupScheme.Torus.Induced
import Langlands.GroupScheme.ZExtension
import Mathlib.FieldTheory.IsSepClosed

/-! # Injectivity of inertia coinvariants for a central induced torus quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- Proof of KP Proposition 11.5.3, with the argument of the proofs of KP Lemmas 11.1.10
and 11.1.12(2), for an arbitrary closed central induced torus: if `Z` is a closed central
induced torus of the connected reductive group `H` and `G` is the fppf quotient of `H` by
the full subgroup functor of `Z`, then the actual selected map `π₁(Z)_I → π₁(H)_I` is
injective. -/
def InducedCentralTorusInertiaInjectivityStatement : Prop :=
  ∀ (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K]
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (hZ : IsInducedTorus Z)
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H), IsConnectedReductive G →
    ∀ (i : Z.toGrp ⟶ H) (p : H ⟶ G),
    IsClosedSubgroup i → IsCentral i →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
    Function.Injective
      (fundamentalInertiaMap k K E H hH Z.toGrp
        hZ.isTorus.isConnectedReductive_of_fieldSplitting i)

/-- The z-extension case (KP Proposition 11.5.3): for every z-extension `z` of `G`, the map
`π₁(Z)_I → π₁(H)_I` induced by `z.i` is injective. -/
theorem InducedCentralTorusInertiaInjectivityStatement.zExtension
    (h : InducedCentralTorusInertiaInjectivityStatement.{u})
    (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : ZExtension G) :
    Function.Injective
      (fundamentalInertiaMap k K E z.H z.isZExtension.source_reductive z.Z.toGrp
        z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting z.i) :=
  h k K E z.Z z.isZExtension.induced z.H G z.isZExtension.source_reductive
    z.isZExtension.target_reductive z.i z.p z.isZExtension.closed z.isZExtension.central
    z.isZExtension.quotient

end Langlands.Geometry.Building.Kottwitz
