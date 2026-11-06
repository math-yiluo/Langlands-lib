import Langlands.Representation.RankinSelberg.TemperedLFactorGamma

noncomputable section

namespace Langlands.RankinSelberg

namespace SegmentGammaTelescoping

open Polynomial

/-- A normalized linear Euler polynomial with nonzero reciprocal-root parameter. -/
def linearFactor (a : ℂˣ) : ℂ[X] := 1 - C (a : ℂ) * X

/-- The exponent of a pair of centered segment blocks. -/
def blockExponent (m n i j : ℕ) : ℤ := (m : ℤ) + n - 2 * i - 2 * j

/-- The polynomial of the full rectangular family for one parameter. -/
def fullPolynomial (a t : ℂˣ) (m n : ℕ) : ℂ[X] :=
  ∏ i : Fin (m + 1), ∏ j : Fin (n + 1),
    linearFactor (a * t ^ blockExponent m n i.val j.val)

/-- The first row of the rectangular family for one parameter. -/
def boundaryPolynomial (a t : ℂˣ) (m n : ℕ) : ℂ[X] :=
  ∏ j : Fin (n + 1), linearFactor (a * t ^ blockExponent m n 0 j.val)

end SegmentGammaTelescoping

open SegmentGammaTelescoping TemperedLFactorGamma

/-- Rectangular centered linear products have the same reflected ratio as the
first row, up to a nonzero Laurent monomial. -/
def SegmentGammaTelescopingStatement : Prop :=
  ∀ (A : Finset ℂˣ) (t : ℂˣ) (m n : ℕ),
    Nonempty (ReflectedRatioData (t ^ 2)
      (∏ a ∈ A, fullPolynomial a t m n)
      (∏ a ∈ A, fullPolynomial a⁻¹ t⁻¹ m n)
      (∏ a ∈ A, boundaryPolynomial a t m n)
      (∏ a ∈ A, boundaryPolynomial a⁻¹ t m n))

end Langlands.RankinSelberg
