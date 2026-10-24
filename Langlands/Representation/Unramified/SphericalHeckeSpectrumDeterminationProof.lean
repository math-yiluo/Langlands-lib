import Langlands.Representation.Unramified.SphericalHeckeDetermination
import Langlands.Representation.Unramified.SphericalHeckeGenerationProof

/-! # Standard Hecke scalars determine spherical irreducible representations -/

namespace Langlands.Unramified

universe uF uV uW

/-- Two actual irreducible admissible spherical objects whose standard Hecke operators
act by the scalars of one common multiset are equivalent. -/
theorem sphericalHeckeSpectrumDetermination :
    SphericalHeckeSpectrumDeterminationStatement.{uF, uV, uW} :=
  sphericalHeckeSpectrumDetermination_of sphericalHeckeGeneration.{uF}

end Langlands.Unramified
