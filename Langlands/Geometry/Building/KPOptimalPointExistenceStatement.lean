import Langlands.Geometry.Building.KPOptimalPoints

/-! # Existence of a rational optimal point (KP §13.4) -/

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

open GalleryGeometry

/-- For an affine root system with the corrected axioms and a positive rational period,
every nonempty finite subset of the strip of a fixed chamber admits a rational max–min
point in the closed chamber. This is the existence assertion following KP Definition 13.4.2,
expressed using the affine-root axioms. -/
def OptimalPointExistenceStatement : Prop :=
  ∀ (V : Type u) (A : Type v) [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (Ψ : Set (A →ᵃ[ℝ] ℝ)), IsAffineRootSystemWithRankZero Ψ →
    (rationalRootPeriods Ψ).Nonempty → ∀ (c : A), IsRegular Ψ c →
      ∀ (S : Finset (A →ᵃ[ℝ] ℝ)), S.Nonempty →
        (↑S : Set (A →ᵃ[ℝ] ℝ)) ⊆ positiveRootsBelowPeriod Ψ c →
        ∃ x : A, IsOptimalPointFor Ψ c S x

end Langlands.Geometry.Building.AffineRootSystem
