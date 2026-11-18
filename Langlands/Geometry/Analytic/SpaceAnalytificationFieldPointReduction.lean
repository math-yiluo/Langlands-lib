import Langlands.Geometry.Analytic.FieldPointSaturation
import Langlands.Geometry.Analytic.SpaceAnalytificationFieldPointsStatement
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsStatement

/-!
# Base-field points and the remaining analytification descent

The underlying-point projection is injective for every analytic space. The affine
rational-point comparison constructs the canonical field-valued point attached to an
algebraic point. This reduces the algebraic-space comparison to injectivity and the
image of the underlying rational-point map.
-/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory SaturatedAtlasPresentation AffinoidAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

section Projection

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Base-field-valued points on any affinoid atlas have injective point projection. -/
theorem fieldPoint_point_injective (A : AffinoidAtlasPresentation.{u, v, w} K) :
    Function.Injective (FieldPoint.point (L := K) (A := A)) :=
  fun _ _ h => FieldPointSaturationComparison.fieldPoint_ext h

/-- The underlying-point projection for base-field-valued points is injective on the
entire localized category, without any algebraic-space or separatedness hypothesis. -/
theorem localizedFieldPointProjection_injective
    (Y : LocalizedCategory.{u, v, w} (K := K)) :
    Function.Injective ((localizedFieldPointProjection K).app Y) := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective Y
  intro p q hpq
  apply fieldPoint_point_injective A.presentation
  exact congrArg ULift.down hpq

end Projection

namespace SpaceAnalytification

variable (hAffine : AffineAnalytification.AffineAnalytificationRationalPointsStatement.{u, u})
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The identity base-field point, using the explicitly supplied affine comparison. -/
def identityFieldPointOfAffineComparison (P₀ : FinitePolynomialPresentation K K) :
    (localizedFieldPointFunctor K).obj (AffineAnalytification.localized K P₀) :=
  (hAffine K K P₀).2.2.choose (AlgPoint.ofAlgHom (AlgHom.id K K))

theorem identityFieldPointOfAffineComparison_point (P₀ : FinitePolynomialPresentation K K) :
    ULift.down ((localizedFieldPointProjection K).app (AffineAnalytification.localized K P₀)
      (identityFieldPointOfAffineComparison hAffine K P₀)) =
        AffineAnalytification.analyticPoint K P₀ (AlgPoint.ofAlgHom (AlgHom.id K K)) :=
  (hAffine K K P₀).2.2.choose_spec _

variable {K}
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}
variable {Y : LocalizedCategory.{u, u, u} (K := K)}

/-- The field-valued point obtained by mapping the identity point along the map attached
to an algebraic `K`-point. No analytification laws are needed for this construction. -/
def rationalFieldPointOfAffineComparison (p : PointFamily K X Y)
    (P₀ : FinitePolynomialPresentation K K) (x : RingPoints K X K) :
    (localizedFieldPointFunctor K).obj Y :=
  (localizedFieldPointFunctor K).map (p K P₀ x)
    (identityFieldPointOfAffineComparison hAffine K P₀)

/-- The constructed field-valued point has the prescribed underlying rational point. -/
theorem rationalFieldPointOfAffineComparison_point (p : PointFamily K X Y)
    (P₀ : FinitePolynomialPresentation K K) (x : RingPoints K X K) :
    ULift.down ((localizedFieldPointProjection K).app Y
      (rationalFieldPointOfAffineComparison hAffine p P₀ x)) = rationalPoint p P₀ x := by
  have hn := congrArg
    (fun f => f (identityFieldPointOfAffineComparison hAffine K P₀))
    ((localizedFieldPointProjection K).naturality (p K P₀ x))
  have hd := congrArg ULift.down hn
  change ULift.down ((localizedFieldPointProjection K).app Y
      (rationalFieldPointOfAffineComparison hAffine p P₀ x)) =
    localizedSpaceFunctor.map (p K P₀ x)
      (ULift.down ((localizedFieldPointProjection K).app (AffineAnalytification.localized K P₀)
        (identityFieldPointOfAffineComparison hAffine K P₀))) at hd
  rw [identityFieldPointOfAffineComparison_point] at hd
  exact hd

include hAffine in
/-- An injective rational-point map whose image contains every base-field-valued point
gives the required point-preserving equivalence. The image condition is retained as a
premise; it is the algebraic-space descent obligation. -/
theorem fieldPointEquiv_of_rationalPoint_image (p : PointFamily K X Y)
    (P₀ : FinitePolynomialPresentation K K)
    (hinj : Function.Injective (rationalPoint p P₀))
    (himage : ∀ q : (localizedFieldPointFunctor K).obj Y,
      ∃ x : RingPoints K X K,
        rationalPoint p P₀ x = ULift.down ((localizedFieldPointProjection K).app Y q)) :
    ∃ e : RingPoints K X K ≃ (localizedFieldPointFunctor K).obj Y,
      ∀ x, ULift.down ((localizedFieldPointProjection K).app Y (e x)) =
        rationalPoint p P₀ x := by
  let f := rationalFieldPointOfAffineComparison hAffine p P₀
  have hf : Function.Bijective f := by
    constructor
    · intro x x' he
      apply hinj
      exact (rationalFieldPointOfAffineComparison_point hAffine p P₀ x).symm.trans
        ((congrArg (fun q => ULift.down ((localizedFieldPointProjection K).app Y q)) he).trans
          (rationalFieldPointOfAffineComparison_point hAffine p P₀ x'))
    · intro q
      obtain ⟨x, hx⟩ := himage q
      refine ⟨x, localizedFieldPointProjection_injective Y ?_⟩
      apply ULift.ext
      exact (rationalFieldPointOfAffineComparison_point hAffine p P₀ x).trans hx
  exact ⟨Equiv.ofBijective f hf, rationalFieldPointOfAffineComparison_point hAffine p P₀⟩

end SpaceAnalytification

end Langlands.Analytic
