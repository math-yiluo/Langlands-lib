import Langlands.AlgebraicGeometry.PointTopology.AffineSchemePullbacks
import Langlands.AlgebraicGeometry.PointTopology.AffinePushoutPoints

/-!
# Points of arbitrary relative affine pullback cones
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {X Y Z : Over (Spec (CommRingCat.of R))}
variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The actual relative points of an arbitrary cone restrict along its two legs. -/
def affineSchemePullbackPointComparison (c : PullbackCone f g)
    (p : RingPoint R c.pt S) :
    {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} :=
  ⟨(p ≫ c.fst, p ≫ c.snd), by
    dsimp only [RingPoint] at p ⊢
    simp only [Category.assoc, c.condition]⟩

/-- The universal property in all schemes over the base gives the actual point
bijection, even when the value spectrum is not of finite type. -/
def affineSchemePullbackPointEquiv (c : PullbackCone f g) (hc : IsLimit c) :
    RingPoint R c.pt S ≃
      {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} where
  toFun := affineSchemePullbackPointComparison R S c
  invFun q := PullbackCone.IsLimit.lift hc q.1.1 q.1.2 q.2
  left_inv p := by
    apply PullbackCone.IsLimit.hom_ext hc <;>
      simp only [PullbackCone.IsLimit.lift_fst, PullbackCone.IsLimit.lift_snd,
        affineSchemePullbackPointComparison]
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact PullbackCone.IsLimit.lift_fst hc _ _ _
    · exact PullbackCone.IsLimit.lift_snd hc _ _ _

@[simp] theorem affineSchemePullbackPointEquiv_apply
    (c : PullbackCone f g) (hc : IsLimit c) (p : RingPoint R c.pt S) :
    affineSchemePullbackPointEquiv R S c hc p =
      affineSchemePullbackPointComparison R S c p := rfl

variable [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]

/-- Compatibility of two actual scheme points is exactly compatibility of
their actual coordinate-algebra maps. -/
theorem affineSchemePointPair_compatible_iff
    (p : RingPoint R X S) (q : RingPoint R Y S) :
    p ≫ f = q ≫ g ↔
      AlgPoint.precomp (affineCoordinatePullback R f)
          (affineSchemePointEquiv R X S p) =
        AlgPoint.precomp (affineCoordinatePullback R g)
          (affineSchemePointEquiv R Y S q) := by
  rw [← affineSchemePointEquiv_natural, ← affineSchemePointEquiv_natural]
  exact (affineSchemePointEquiv R Z S).injective.eq_iff.symm

/-- The factorwise actual point equivalences identify the two compatible-pair
sets. The common point on Z is allowed to vary. -/
def affineSchemeCompatiblePairEquiv :
    {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g} ≃
      {q : AlgPoint R (AffineCoordinateRing R X) S ×
          AlgPoint R (AffineCoordinateRing R Y) S //
        AlgPoint.precomp (affineCoordinatePullback R f) q.1 =
          AlgPoint.precomp (affineCoordinatePullback R g) q.2} where
  toFun q := ⟨(affineSchemePointEquiv R X S q.1.1,
    affineSchemePointEquiv R Y S q.1.2),
    (affineSchemePointPair_compatible_iff R S _ _).mp q.2⟩
  invFun q := ⟨((affineSchemePointEquiv R X S).symm q.1.1,
    (affineSchemePointEquiv R Y S).symm q.1.2), by
      apply (affineSchemePointPair_compatible_iff R S _ _).mpr
      simpa only [Equiv.apply_symm_apply] using q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact Prod.ext (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)
  right_inv q := by
    apply Subtype.ext
    exact Prod.ext (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)

/-- The actual pullback-point comparison commutes with the coordinate pushout
comparison and the genuine global-section point equivalences. -/
theorem affineSchemePullbackPointComparison_coordinates
    (c : PullbackCone f g) [IsAffine c.pt.left] (p : RingPoint R c.pt S) :
    affineSchemeCompatiblePairEquiv R S
        (affineSchemePullbackPointComparison R S c p) =
      affinePushoutPointComparison R S (affineCoordinatePushout R c)
        (affineSchemePointEquiv R c.pt S p) := by
  apply Subtype.ext
  apply Prod.ext
  · exact affineSchemePointEquiv_natural R S c.fst p
  · exact affineSchemePointEquiv_natural R S c.snd p

end Langlands.AlgebraicGeometry.PointTopology
