import Langlands.Algebra.AdicCompleteSurjection
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardSourceTower

/-! # Completeness of the actual Picard source quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceTower

open Langlands.AlgebraicGeometry.Deformation ArtinianPicardSourceStep

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The actual source quotient determined by all tower equations is complete local. -/
instance limitRing_isAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (limitRing ε hε f M s₀))
      (limitRing ε hε f M s₀) :=
  Langlands.Algebra.AdicCompleteSurjection.complete_of_surjective
    (Ideal.Quotient.mk (limitingEquations ε hε f M s₀)) Ideal.Quotient.mk_surjective

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardSourceTower
