import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect

/-! # Points of defect zero lie in the smooth locus -/

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Let `R` be a discrete valuation ring with uniformizer `ϖ` and `A` an `R`-algebra of finite
type whose localization `A[1/ϖ]` (the generic fibre) is smooth over `R`. If a point
`φ : A →ₐ[R] R'` with values in a discrete valuation ring `R'` of ramification index one over
`R` has defect zero, then `A` is smooth over `R` at the prime `φ⁻¹(𝔪_{R'})`. -/
def DefectZeroSmoothAtStatement : Prop :=
  ∀ (R A R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (ϖ : R), Irreducible ϖ → IsRamificationIndexOne R R' →
    Algebra.Smooth R (Localization.Away (algebraMap R A ϖ)) →
    ∀ φ : A →ₐ[R] R', pointDefect φ = 0 →
      (⟨(IsLocalRing.maximalIdeal R').comap φ, Ideal.comap_isPrime _ _⟩ : PrimeSpectrum A) ∈
        Algebra.smoothLocus R A

end Langlands.AlgebraicGeometry.DvrSmoothening
