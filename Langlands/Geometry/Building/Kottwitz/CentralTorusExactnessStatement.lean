import Langlands.Geometry.Building.Kottwitz.FundamentalGroup
import Langlands.GroupScheme.ZExtension
import Mathlib.FieldTheory.IsSepClosed

/-! # Right exactness of inertia coinvariants for a central torus quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- An induced torus is a torus (module-local helper for the z-extension case). -/
private theorem isTorus_of_isInducedTorus {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))} (h : IsInducedTorus Z) :
    IsTorus Z.toGrp := by
  obtain ⟨L, hL, aL, -, -, hs, -⟩ := h
  exact ⟨L, hL, aL, hs⟩

/-- KP proofs of Lemma 11.5.1 and Proposition 11.5.3, for an arbitrary central
torus: if `Z` is a closed central torus of `H` and `G` is the fppf quotient of
`H` by the full subgroup functor of `Z`, then
`π₁(Z)_I → π₁(H)_I → π₁(G)_I → 0` is exact for the actual selected descended
maps. Injectivity on the left is not asserted. -/
def CentralTorusInertiaExactnessStatement : Prop :=
  ∀ (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K]
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (hZ : IsTorus Z.toGrp)
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
    (i : Z.toGrp ⟶ H) (p : H ⟶ G),
    IsClosedSubgroup i → IsCentral i →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
    Function.Surjective (fundamentalInertiaMap k K E G hG H hH p) ∧
      LinearMap.ker (fundamentalInertiaMap k K E G hG H hH p) =
        LinearMap.range
          (fundamentalInertiaMap k K E H hH Z.toGrp
            hZ.isConnectedReductive_of_fieldSplitting i)

/-- The induced-torus special case: for every z-extension, the inertia map of
the projection is surjective and its kernel is the image of `π₁(Z)_I`. -/
theorem CentralTorusInertiaExactnessStatement.zExtension
    (h : CentralTorusInertiaExactnessStatement.{u})
    (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : ZExtension G) :
    Function.Surjective
        (fundamentalInertiaMap k K E G z.isZExtension.target_reductive z.H
          z.isZExtension.source_reductive z.p) ∧
      LinearMap.ker
          (fundamentalInertiaMap k K E G z.isZExtension.target_reductive z.H
            z.isZExtension.source_reductive z.p) =
        LinearMap.range
          (fundamentalInertiaMap k K E z.H z.isZExtension.source_reductive z.Z.toGrp
            (isTorus_of_isInducedTorus
              z.isZExtension.induced).isConnectedReductive_of_fieldSplitting
            z.i) :=
  h k K E z.Z (isTorus_of_isInducedTorus z.isZExtension.induced) z.H G
    z.isZExtension.source_reductive z.isZExtension.target_reductive z.i z.p
    z.isZExtension.closed z.isZExtension.central z.isZExtension.quotient

end Langlands.Geometry.Building.Kottwitz
