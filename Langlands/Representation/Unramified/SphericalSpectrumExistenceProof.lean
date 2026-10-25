import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof
import Langlands.Representation.Unramified.ConstituentHeckeScalarProof
import Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! # Exhaustion of spherical representations by normalized principal series -/

namespace Langlands.Unramified

open Correspondence

universe uF uV

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology

/-- Every actual irreducible admissible spherical representation occurs as a
subquotient of a normalized unramified principal series. -/
theorem sphericalSpectrumExistence :
    SphericalSpectrumExistenceStatement.{uF, uV} := by
  intro p _ F r A hA
  obtain ⟨s, hs⟩ := sphericalHeckeSpectrumExistence p F r A hA
  obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
  obtain ⟨B, hB⟩ := SphericalExistence.sphericalConstituentExistence p F r z
  have hBs : HasSphericalHeckeSpectrum F B s := by
    rw [← hz]
    exact sphericalConstituentHeckeScalar p F r z B hB
  obtain ⟨e⟩ := sphericalHeckeSpectrumDetermination p F r A B s hs hBs
  exact ⟨s, z, hz, (isSphericalConstituent_iff_of_equiv F z e).mpr hB⟩

end Langlands.Unramified
