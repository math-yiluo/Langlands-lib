import Langlands.Representation.Unramified.ConstituentHeckeScalarStatement
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Standard Hecke scalars of spherical principal-series constituents -/

namespace Langlands.Unramified

universe uF uV

/-- Every spherical principal-series constituent has the standard Hecke scalars
of its inducing spectrum, with independent field and carrier universes. -/
theorem sphericalConstituentHeckeScalar :
    SphericalConstituentHeckeScalarStatement.{uF, uV} := by
  intro p _ F r z A h
  exact hasSphericalHeckeSpectrum_of_isSphericalConstituent F h

end Langlands.Unramified
