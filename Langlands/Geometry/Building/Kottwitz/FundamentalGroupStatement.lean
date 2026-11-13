import Langlands.Geometry.Building.Kottwitz.FundamentalGroup
import Mathlib.FieldTheory.IsSepClosed

/-! # Fundamental-group inertia descent and torus comparison targets -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Fact 11.3.5: the representative-characterized comparison for a torus
exists uniquely and is a Galois-equivariant isomorphism. -/
def TorusFundamentalComparisonStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp),
    (∃! m, IsTorusFundamentalComparison k E T hT m) ∧
    IsTorusFundamentalComparison k E T hT (torusFundamentalComparison k E T hT) ∧
    Function.Bijective (torusFundamentalComparison k E T hT) ∧
    (∀ (σ : E ≃ₐ[k] E)
      (x : fundamentalGroup k T.toGrp E hT.isConnectedReductive_of_fieldSplitting),
      torusFundamentalComparison k E T hT
        (fundamentalGroupGalois k T.toGrp E hT.isConnectedReductive_of_fieldSplitting σ x) =
      cocharacterLattice.galoisRepresentation k E T σ (torusFundamentalComparison k E T hT x))

/-- Inertia descent of KP Lemma 11.3.6, with unique descent, residual equivariance,
identities and composition. These conclusions are not premises of the selected maps. -/
def FundamentalInertiaMapStatement : Prop :=
  ∀ (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K] [Normal k E],
    (∀ (H G : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G),
      (∃! m, IsFundamentalInertiaMap k K E G hG H hH f m) ∧
      IsFundamentalInertiaMap k K E G hG H hH f
        (fundamentalInertiaMap k K E G hG H hH f) ∧
      (∀ (σ : K ≃ₐ[k] K) (x : FundamentalInertia k K E H hH),
        fundamentalInertiaMap k K E G hG H hH f
          (fundamentalGammaRepresentation k K E H hH σ x) =
        fundamentalGammaRepresentation k K E G hG σ
          (fundamentalInertiaMap k K E G hG H hH f x))) ∧
    (∀ (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      fundamentalInertiaMap k K E G hG G hG (𝟙 G) = LinearMap.id) ∧
    (∀ (H G J : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hG : IsConnectedReductive G)
      (hJ : IsConnectedReductive J) (f : H ⟶ G) (g : G ⟶ J),
      (fundamentalInertiaMap k K E J hJ G hG g).comp
        (fundamentalInertiaMap k K E G hG H hH f) =
      fundamentalInertiaMap k K E J hJ H hH (f ≫ g))

/-- The identification of the reductive and torus inertia targets is uniquely
determined on representatives, bijective and equivariant for the actual residual group. -/
def TorusInertiaComparisonStatement : Prop :=
  ∀ (k K E : Type u) [Field k] [Field K] [Field E]
    [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [IsSepClosure k E] [Normal k K] [Normal k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp),
    (∃! m, IsTorusInertiaComparison k K E T hT m) ∧
    IsTorusInertiaComparison k K E T hT (torusInertiaComparison k K E T hT) ∧
    Function.Bijective (torusInertiaComparison k K E T hT) ∧
    (∀ (σ : K ≃ₐ[k] K)
      (x : FundamentalInertia k K E T.toGrp hT.isConnectedReductive_of_fieldSplitting),
      torusInertiaComparison k K E T hT
        (fundamentalGammaRepresentation k K E T.toGrp
          hT.isConnectedReductive_of_fieldSplitting σ x) =
      torusGammaRepresentation k K E T σ (torusInertiaComparison k K E T hT x))

end Langlands.Geometry.Building.Kottwitz
