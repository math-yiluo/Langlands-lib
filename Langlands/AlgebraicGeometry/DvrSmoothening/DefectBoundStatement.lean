import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.PointDefect

/-! # Boundedness of the defect of smoothness -/

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- Let `R` be a discrete valuation ring with uniformizer `ϖ` and `A` an `R`-algebra of finite
type whose localization `A[1/ϖ]` is smooth over `R`. Then the defect of smoothness is bounded
on all points of `A` with values in discrete valuation rings of ramification index one over
`R`. -/
def DefectBoundStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] (ϖ : R), Irreducible ϖ →
    Algebra.Smooth R (Localization.Away (algebraMap R A ϖ)) →
    ∃ n : ℕ, ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      [Algebra R R'] [IsLocalHom (algebraMap R R')], IsRamificationIndexOne R R' →
      ∀ φ : A →ₐ[R] R', pointDefect φ ≤ n

end Langlands.AlgebraicGeometry.DvrSmoothening
