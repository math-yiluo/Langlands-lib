import Langlands.Correspondence.FullSpecification
import Langlands.Correspondence.SphericalStandardLComparisonProof
import Langlands.Correspondence.StandardLPolynomial
import Langlands.Correspondence.UnramifiedSpectrumClass
import Langlands.Representation.Unramified.SphericalConstituentChoice
import Langlands.Representation.Unramified.SphericalSpectrumExistenceProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-!
# Unramified normalization for every full correspondence

The published spherical standard L comparison and the arithmetic Euler converse
identify every unramified parameter image and prove the unchanged full target.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Unramified

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fullUnramifiedFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance fullUnramifiedGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Every full correspondence satisfies the spherical and principal-series
normalization for every geometrically normalized reciprocity candidate, with
independent field, parameter and representation carrier universes. -/
theorem fullCorrespondenceUnramified :
    FullCorrespondenceUnramifiedStatement.{uF, uP, uA} F := by
  classical
  have hcmp := sphericalStandardLComparison.{uF, uA} F
  intro c e hc he
  obtain ⟨hbij, _, e0, _, hrankOne, _, _, hfactor⟩ := hc
  obtain ⟨D0, hD0, hπ0⟩ := hrankOne 1
  have htriv : weilCharacter F e0 1 = 1 := by
    ext w
    rfl
  rw [htriv] at hD0
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F
    F.canonicalTopologicalData
  obtain ⟨ν, hν⟩ := (hfactor.1 ψ 0 0 D0 D0).1
  have hpolynomial (r : ℕ) (D : WeilDeligneClass.{uF, uP} F r.succPNat)
      (s : Eigenvalues (r + 1))
      (hs : HasSphericalSpectrumClass F (c r.succPNat D) s) :
      parameterEulerPolynomial F D = Eigenvalues.eulerPolynomial s := by
    exact hcmp ψ ν hν r (c r.succPNat D) (c 1 D0) s
      (parameterEulerPolynomial F D) hπ0 hs
      (IsPairLCompatibleAt.standardEulerPolynomial F ψ
        (hfactor.1 ψ r 0 D D0) hD0 ν hν)
  have hpreimage (r : ℕ) (z : Fin (r + 1) → ℂˣ) :
      c r.succPNat (unramifiedSpectrumClass.{uF, uP} F (Eigenvalues.ofTuple z)) =
        automorphicClassOf F (sphericalConstituentOfTuple.{uF, uA} F z) := by
    obtain ⟨E, hE⟩ := (hbij r.succPNat).2
      (automorphicClassOf F (sphericalConstituentOfTuple.{uF, uA} F z))
    have hs : HasSphericalSpectrumClass F (c r.succPNat E) (Eigenvalues.ofTuple z) := by
      rw [hE]
      exact sphericalConstituentOfTuple_hasSpectrum F z
    have hparameter : E = unramifiedSpectrumClass F (Eigenvalues.ofTuple z) :=
      (parameterEulerPolynomial_eq_eulerPolynomial_iff _).mp (hpolynomial r E _ hs)
    simpa only [hparameter] using hE
  constructor
  · intro r D
    constructor
    · intro hD
      obtain ⟨s, hDs⟩ := isUnramifiedParameterClass_iff_exists_unramifiedSpectrumClass.mp hD
      obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective (r + 1) s
      rw [hDs, ← hz, hpreimage]
      exact (sphericalConstituentOfTuple_hasSpectrum F z).isSpherical
    · rintro ⟨A, hA, hfixed⟩
      obtain ⟨s, hs⟩ := sphericalSpectrumExistence p F r A hfixed
      exact isUnramifiedParameterClass_iff_exists_eulerPolynomial.mpr
        ⟨s, hpolynomial r D s ⟨A, hA, hs⟩⟩
  · intro r χ hχ
    let z := characterValues F χ
    let D := unramifiedSpectrumClass.{uF, uP} F (Eigenvalues.ofTuple z)
    let A := sphericalConstituentOfTuple.{uF, uA} F z
    have hA := sphericalConstituentOfTuple_spec.{uF, uA} F z
    refine ⟨D, ?_, A, (hpreimage r z).symm, hA.1, ?_⟩
    · exact (isCharacterSumParameter_iff_eq_unramifiedSpectrumClass he hχ).mpr rfl
    · change IsSubquotientOf (principalSeries F r χ) A.obj.representation
      have hsub := hA.2
      change IsSubquotientOf (principalSeries F r (characterTuple F z))
        A.obj.representation at hsub
      rwa [characterTuple_characterValues F χ hχ] at hsub

end Langlands.Correspondence
