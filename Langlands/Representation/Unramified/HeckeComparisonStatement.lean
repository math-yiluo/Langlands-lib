import Langlands.Representation.Unramified.HeckeOperators

/-! # Normalized principal-series and actual spherical Hecke comparison -/

namespace Langlands.Unramified

open Correspondence

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An unordered normalized principal-series spectrum is exactly the spectrum
of the actual standard spherical double-coset operators with the positive
square-root residue normalization. This is an unproved comparison obligation. -/
def SphericalHeckeComparisonStatement : Prop :=
  ∀ (r : ℕ) (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (s : Eigenvalues (r + 1)),
    HasSphericalSpectrum F A s ↔ HasSphericalHeckeSpectrum F A s

end Langlands.Unramified
