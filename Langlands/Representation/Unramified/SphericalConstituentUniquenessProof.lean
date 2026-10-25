import Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationProof
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Spherical constituent uniqueness across unordered principal-series parameters -/

namespace Langlands.Unramified

universe uF uV uW

/-- Spherical constituents of normalized principal series with the same unordered
uniformizer spectrum are equivalent, for independent carrier universes. -/
theorem sphericalConstituentUniqueness :
    SphericalConstituentUniquenessStatement.{uF, uV, uW} :=
  sphericalConstituentUniqueness_of
    (fun _ _ F _ _ _ h => hasSphericalHeckeSpectrum_of_isSphericalConstituent F h)
    (fun _ _ F _ _ _ h => hasSphericalHeckeSpectrum_of_isSphericalConstituent F h)
    sphericalHeckeSpectrumDetermination

end Langlands.Unramified
