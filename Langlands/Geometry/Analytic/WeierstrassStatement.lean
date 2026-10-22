import Langlands.Geometry.Analytic.RestrictedSeriesDefinitions

/-! # Analytic Weierstrass division and preparation at unit radius -/

universe u

namespace Langlands.Analytic.RestrictedSeries

/-- Existence and uniqueness of norm-controlled division by a distinguished
restricted series, with an actual polynomial remainder. -/
def DistinguishedDivisionStatement (A : Type u) [NormedCommRing A]
    [IsUltrametricDist A] [Nontrivial A] [NormOneClass A] [NormMulClass A]
    [CompleteSpace A] : Prop :=
  ∀ (f : Algebra A) (d : ℕ), IsDistinguished f d → ∀ g : Algebra A,
    ∃! qr : Algebra A × Polynomial A,
      g = f * qr.1 + ofPolynomial A qr.2 ∧ qr.2.degree < d ∧
      ‖f * qr.1‖ ≤ ‖g‖ ∧ ‖ofPolynomial A qr.2‖ ≤ ‖g‖

/-- Existence and uniqueness of preparation with a genuine unit and a monic
polynomial of the distinguished degree whose coefficients lie in the unit ball. -/
def DistinguishedPreparationStatement (A : Type u) [NormedCommRing A]
    [IsUltrametricDist A] [Nontrivial A] [NormOneClass A] [NormMulClass A]
    [CompleteSpace A] : Prop :=
  ∀ (f : Algebra A) (d : ℕ), IsDistinguished f d →
    ∃! ew : (Algebra A)ˣ × Polynomial A,
      f = (ew.1 : Algebra A) * ofPolynomial A ew.2 ∧
      ew.2.Monic ∧ ew.2.natDegree = d ∧ ∀ n, ‖ew.2.coeff n‖ ≤ 1

/-- The combined division and preparation target. -/
def WeierstrassStatement (A : Type u) [NormedCommRing A]
    [IsUltrametricDist A] [Nontrivial A] [NormOneClass A] [NormMulClass A]
    [CompleteSpace A] : Prop :=
  DistinguishedDivisionStatement A ∧ DistinguishedPreparationStatement A

end Langlands.Analytic.RestrictedSeries
