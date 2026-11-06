import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Spherical constituents in independent carrier universes

A chosen actual spherical constituent can be realized in any prescribed
carrier universe using the published small-realization theorem.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance choiceFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance choiceGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Every tuple has an actual spherical constituent in an independently
prescribed carrier universe. -/
theorem exists_sphericalConstituentOfTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    ∃ A : AutomorphicObject.{uF, uA} F r.succPNat, IsSphericalConstituent F z A := by
  obtain ⟨B, hB⟩ := SphericalExistence.sphericalConstituentExistence p F r z
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uF, uA}
      p F F.canonicalTopologicalData (r + 1) B.obj B.property.1
  let A : AutomorphicObject.{uF, uA} F r.succPNat :=
    ⟨K, hK, isAdmissible_of_equiv e B.property.2⟩
  exact ⟨A, (isSphericalConstituent_iff_of_equiv F z e).mp hB⟩

/-- A choice of an actual spherical constituent of the normalized principal
series with uniformizer tuple `z`, in the specified carrier universe. -/
def sphericalConstituentOfTuple {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    AutomorphicObject.{uF, uA} F r.succPNat :=
  Classical.choose (exists_sphericalConstituentOfTuple.{uF, uA} F z)

theorem sphericalConstituentOfTuple_spec {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    IsSphericalConstituent F z (sphericalConstituentOfTuple.{uF, uA} F z) :=
  Classical.choose_spec (exists_sphericalConstituentOfTuple.{uF, uA} F z)

theorem sphericalConstituentOfTuple_hasSpectrum {r : ℕ} (z : Fin (r + 1) → ℂˣ) :
    HasSphericalSpectrumClass F
      (automorphicClassOf F (sphericalConstituentOfTuple.{uF, uA} F z))
      (Eigenvalues.ofTuple z) := by
  refine ⟨sphericalConstituentOfTuple F z, rfl, z, rfl, ?_⟩
  exact sphericalConstituentOfTuple_spec F z

end Langlands.Unramified
