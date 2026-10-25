import Langlands.Representation.Unramified.HeckeComparisonStatement
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof
import Langlands.Representation.Unramified.SphericalHeckeSpectrumDeterminationProof
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof

/-! # Normalized principal-series and spherical Hecke spectra agree -/

namespace Langlands.Unramified

open Correspondence

universe uF uV

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology

/-- The normalized principal-series spectrum agrees with the spectrum of the actual
standard spherical Hecke operators on the original representation. -/
theorem sphericalHeckeComparison
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    SphericalHeckeComparisonStatement.{uF, uV} F := by
  intro r A s
  constructor
  · rintro ⟨z, rfl, hA⟩
    exact hasSphericalHeckeSpectrum_of_isSphericalConstituent F hA
  · intro hA
    obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
    obtain ⟨B, hB⟩ := SphericalExistence.sphericalConstituentExistence p F r z
    have hBs : HasSphericalHeckeSpectrum F B s := by
      rw [← hz]
      exact hasSphericalHeckeSpectrum_of_isSphericalConstituent F hB
    obtain ⟨e⟩ := sphericalHeckeSpectrumDetermination.{uF, uV, uF} p F r A B s hA hBs
    exact ⟨z, hz, (isSphericalConstituent_iff_of_equiv F z e).mpr hB⟩

end Langlands.Unramified
