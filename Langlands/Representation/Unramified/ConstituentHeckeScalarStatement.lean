import Langlands.Representation.Unramified.HeckeOperators

/-! # Standard Hecke scalars of spherical principal-series constituents -/

namespace Langlands.Unramified

open Correspondence

universe uF uV

/-- Every spherical constituent of the ordered normalized principal series of `z`
has the standard spherical Hecke scalars of the unordered spectrum of `z`. -/
def SphericalConstituentHeckeScalarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (z : Fin (r + 1) → ℂˣ) (A : AutomorphicObject.{uF, uV} F r.succPNat),
    IsSphericalConstituent F z A → HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z)

end Langlands.Unramified
