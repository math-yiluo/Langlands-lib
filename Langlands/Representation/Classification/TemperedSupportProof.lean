import Langlands.Representation.Exponents.WeakMinimalExistenceProof
import Langlands.Representation.Exponents.WeakCriticalSupportProof

/-!
# Discrete-series opposite support of irreducible tempered representations

Minimal standard-pair existence and prescribed weakly critical support give
the closed analytic support theorem in the original carrier universe.
-/

namespace Langlands

universe uF uV

/-- An irreducible analytically tempered representation embeds in normalized
opposite induction from irreducible discrete-series product-Levi data. -/
theorem glTemperedDiscreteSeriesSupport :
    GLTemperedDiscreteSeriesSupportStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn V _ _ π hirr htemp
  let A : Rep.{uV} ℂ (GeneralLinear n F.Carrier) := Rep.of π
  obtain ⟨B, hB⟩ :=
    glWeaklyMinimalStandardPairExistence.{uF, uV} p F T n hn A hirr htemp
  obtain ⟨χ, hχ⟩ := hB.isWeaklyCriticalPair T
  obtain ⟨S, hS, _hscalar, hSI, j, hj⟩ :=
    glWeaklyCriticalDiscreteSeriesSupport.{uF, uV} p F T n hn B A hirr htemp χ hχ
  exact ⟨B, S, inferInstance, inferInstance, S.ρ, hS.1, hSI, j, hj⟩

end Langlands
