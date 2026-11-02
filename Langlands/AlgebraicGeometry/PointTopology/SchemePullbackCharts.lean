import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbackPoints
import Mathlib.Topology.Constructions.SumProd

/-! # Actual relative pullbacks and compatible point charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- A relative pullback cone whose underlying scheme is the usual scheme pullback. -/
def relativeSchemePullback {X Y Z : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Z) (g : Y ⟶ Z) : PullbackCone f g := by
  let P := Over.mk (pullback.fst f.left g.left ≫ X.hom)
  let a : P ⟶ X := Over.homMk (pullback.fst f.left g.left)
  let b : P ⟶ Y := Over.homMk (pullback.snd f.left g.left) (by
    change pullback.snd f.left g.left ≫ Y.hom = pullback.fst f.left g.left ≫ X.hom
    rw [← Over.w g, ← Over.w f, ← Category.assoc, ← Category.assoc,
      pullback.condition])
  exact PullbackCone.mk a b (by
    apply Over.OverMorphism.ext
    exact pullback.condition)

/-- The relative cone is limiting in actual schemes over the base. -/
def relativeSchemePullbackIsLimit {X Y Z : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Z) (g : Y ⟶ Z) : IsLimit (relativeSchemePullback R f g) := by
  have h : IsPullback (relativeSchemePullback R f g).fst
      (relativeSchemePullback R f g).snd f g := by
    apply IsPullback.of_map_of_faithful (Over.forget (Spec (CommRingCat.of R)))
    exact IsPullback.of_hasPullback f.left g.left
  exact h.isLimit

instance {X Y Z : Over (Spec (CommRingCat.of R))}
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    (f : X ⟶ Z) (g : Y ⟶ Z) : IsAffine (relativeSchemePullback R f g).pt.left :=
  inferInstanceAs (IsAffine (pullback f.left g.left))

variable [TopologicalSpace S] [IsTopologicalRing S]

/-- The actual affine pullback comparison, without a finiteness assumption. -/
def affineSchemePullbackPointHomeomorph
    {X Y Z : Over (Spec (CommRingCat.of R))}
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
    [IsAffine c.pt.left] (hc : IsLimit c) :
    RingPoint R c.pt S ≃ₜ
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} := by
  let H :
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} ≃ₜ
        {q : AlgPoint R (AffineCoordinateRing R X) S ×
            AlgPoint R (AffineCoordinateRing R Y) S //
          AlgPoint.precomp (affineCoordinatePullback R f) q.1 =
            AlgPoint.precomp (affineCoordinatePullback R g) q.2} :=
    ((affineSchemePointHomeomorph R X S).prodCongr
    (affineSchemePointHomeomorph R Y S)).subtype
      (fun q => affineSchemePointPair_compatible_iff R S (f := f) (g := g) q.1 q.2)
  let hcoord := affinePushoutPointHomeomorph R S (affineCoordinatePushout R c)
    (affineCoordinatePushoutIsColimit R c hc)
  let h := (affineSchemePointHomeomorph R c.pt S).trans (hcoord.trans H.symm)
  have he : (fun p => h p) = affineSchemePullbackPointComparison R S c := by
    funext p
    apply H.injective
    change H (H.symm (affinePushoutPointComparison R S (affineCoordinatePushout R c)
      (affineSchemePointEquiv R c.pt S p))) = H (affineSchemePullbackPointComparison R S c p)
    rw [Homeomorph.apply_symm_apply]
    exact (affineSchemePullbackPointComparison_coordinates R S c p).symm
  exact IsHomeomorph.homeomorph (affineSchemePullbackPointComparison R S c)
    (by rw [← he]; exact h.isHomeomorph)

end Langlands.AlgebraicGeometry.PointTopology
