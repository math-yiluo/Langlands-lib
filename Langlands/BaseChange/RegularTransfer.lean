import Langlands.BaseChange.RegularOrbitalProfilesFromCharts
import Langlands.BaseChange.RegularOrbitParameters
import Langlands.BaseChange.RegularTransferCharts
import Langlands.BaseChange.RegularTransferReduction

/-! Regular-support transfer from the normalized profiles on the two general linear groups. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology
open Langlands.JacquetLanglands Langlands.TraceFormula
open Langlands.Topology (HasCompactOpenNeighborhoodBasis hasCompactOpenNeighborhoodBasis_of_mathlib)
open SigmaLiftCharacterIdentity (coefficients coefficients_conj continuous_coefficients)

universe u v

private theorem regularTransferProfileExistence : RegularTransferProfileExistenceStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : Module.Finite F E := hσ.1
  have hE := generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) (E := E) n
  let : T2Space (GeneralLinear n E) := hE.t2Space
  let : LocallyCompactSpace (GeneralLinear n E) := hE.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  let RF : Set (GeneralLinear n F) := {γ | IsRegularSemisimple γ}
  let RE : Set (GeneralLinear n E) := {δ | IsSigmaRegular σ l δ}
  let pF : RF → Fin n → F := fun r => coefficients r.val
  let pE : RE → Fin n → F := fun r => normCoefficients hσ r.val
  let θE := (entrywiseAut σ n).toMonoidHom
  have hθE : Continuous θE := continuous_entrywiseAut σ n
  have hB : HasCompactOpenNeighborhoodBasis (Fin n → F) :=
    hasCompactOpenNeighborhoodBasis_of_mathlib
  have hOrbitF (r : RF) (g : GeneralLinear n F) :
      ∃ s : RF, (s : GeneralLinear n F) = twistedConj (MonoidHom.id _) g r ∧ pF s = pF r := by
    let x := twistedConj (MonoidHom.id _) g (r : GeneralLinear n F)
    have heq : coefficients x = coefficients r.val := coefficients_conj g r
    have hx : IsRegularSemisimple x := by
      rw [isRegularSemisimple_iff_separable_coefficients, heq]
      exact (isRegularSemisimple_iff_separable_coefficients _).mp r.property
    exact ⟨⟨x, hx⟩, rfl, heq⟩
  have hOrbitE (r : RE) (g : GeneralLinear n E) :
      ∃ s : RE, (s : GeneralLinear n E) = twistedConj θE g r ∧ pE s = pE r := by
    let x := twistedConj θE g (r : GeneralLinear n E)
    have heq : normCoefficients hσ x = normCoefficients hσ r.val :=
      normCoefficients_twistedConj hσ g r
    have hx : IsSigmaRegular σ l x := by
      rw [isSigmaRegular_iff_separable_normCoefficients hσ, heq]
      exact (isSigmaRegular_iff_separable_normCoefficients hσ _).mp r.property
    exact ⟨⟨x, hx⟩, rfl, heq⟩
  obtain ⟨mF, mE, hmF, hmE, hassoc⟩ := regularOrbitalNormalization F E σ l n hσ μF μE
  refine ⟨mF, mE, pF, pE, ?_, ?_, fun δ γ => normCoefficients_eq_iff_associated hσ γ.property, hassoc⟩
  · exact regularOrbitalProfilesFromCharts (MonoidHom.id _) continuous_id μF RF
      (isOpen_regularSemisimple n) pF (continuous_coefficients.comp continuous_subtype_val)
      hB hOrbitF (fun r => exists_ordinaryRegularOrbitalChart r) mF hmF
  · exact regularOrbitalProfilesFromCharts θE hθE μE RE (isOpen_sigmaRegular hσ n) pE
      ((continuous_normCoefficients hσ).comp continuous_subtype_val)
      hB hOrbitE (fun r => exists_twistedRegularOrbitalChart hσ r) mE hmE

/-- Regularly supported test functions transfer in both directions for cyclic base change. -/
theorem regularTransfer : RegularTransferStatement.{u, v} :=
  regularTransferReduction regularTransferProfileExistence
    (by
      intro F _ E _ _ n γ hγ a b ha hb
      exact commute_of_regular_baseChange hγ ha hb)

end Langlands.BaseChange
