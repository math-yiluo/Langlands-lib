import Langlands.Geometry.Analytic.AffineAnalytificationImmersionProof
import Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeProof

/-! # Semilinear maps on points of affine analytifications -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Topology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} {B : Type w} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)

variable (σ : K →+* K) (hσ : ∀ c, ‖σ c‖ = ‖c‖) (φ : A →+* B)
  (hφ : ∀ c, φ (algebraMap K A c) = algebraMap K B (σ c))

private def semilinearImage (y : Space K Q) : Space K P :=
  ImmersionComparison.pointOfSeminorm K P (BaseChangeComparison.pullback (pointSeminorm K Q y) φ)
    (fun c => by
      change pointSeminorm K Q y (φ (algebraMap K A c)) = ‖c‖
      rw [hφ, pointSeminorm_extendsNorm, hσ])

private theorem pointSeminorm_semilinearImage (y : Space K Q) (a : A) :
    pointSeminorm K P (semilinearImage K P Q σ hσ φ hφ y) a = pointSeminorm K Q y (φ a) := by
  unfold semilinearImage
  exact congrArg (fun ν : MulRingSeminorm A => ν a)
    (ImmersionComparison.pointSeminorm_pointOfSeminorm K P
      (BaseChangeComparison.pullback (pointSeminorm K Q y) φ) _)

/-- Pulling the seminorm back by a ring map semilinear over a norm-preserving
map of the base field gives a continuous map of the actual affine analytic point spaces. -/
def semilinearBaseMap : C(Space K Q, Space K P) :=
  ⟨semilinearImage K P Q σ hσ φ hφ,
    (SeminormComparison.isEmbedding_pointSeminorm K P).continuous_iff.2 <|
      continuous_pi fun a => by
        simpa only [Function.comp_def, pointSeminorm_semilinearImage] using
          (continuous_pointSeminorm_apply K Q (φ a))⟩

/-- The induced point evaluates each algebra element by the original point on its image. -/
@[simp] theorem pointSeminorm_semilinearBaseMap (y : Space K Q) (a : A) :
    pointSeminorm K P (semilinearBaseMap K P Q σ hσ φ hφ y) a = pointSeminorm K Q y (φ a) :=
  pointSeminorm_semilinearImage K P Q σ hσ φ hφ y a

/-- For a base-linear algebra map this is the existing affine analytification on points. -/
theorem semilinearBaseMap_id_base (f : A →ₐ[K] B) :
    semilinearBaseMap K P Q (RingHom.id K) (fun _ => rfl) f.toRingHom f.commutes = baseMap K P Q f := by
  ext y
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_semilinearBaseMap, pointSeminorm_baseMap]
  rfl

end Langlands.Analytic.AffineAnalytification
