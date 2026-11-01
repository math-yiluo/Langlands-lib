import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # Normal stalks of a valuation spectrum -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- An explicit predicate on the actual structure-sheaf stalks. -/
def HasNormalStalks (S : Scheme.{u}) : Prop :=
  ∀ x : S, IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x)

/-- The actual stalks of the spectrum of an integrally closed domain are
integrally closed domains. -/
theorem spec_hasNormalStalks (R : CommRingCat.{u}) [IsDomain R]
    [IsIntegrallyClosed R] : HasNormalStalks (Spec R) := by
  change ∀ x : PrimeSpectrum R,
    IsDomain ((Spec.structureSheaf R).presheaf.stalk x) ∧
      IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk x)
  intro x
  exact ⟨IsLocalization.isDomain_of_atPrime _ x.asIdeal,
    isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors⟩

/-- This includes valuation domains of arbitrary rank, including fields. -/
theorem valuation_spec_hasNormalStalks (R : CommRingCat.{u}) [IsDomain R]
    [ValuationRing R] : HasNormalStalks (Spec R) :=
  spec_hasNormalStalks R

end Langlands.AlgebraicGeometry
