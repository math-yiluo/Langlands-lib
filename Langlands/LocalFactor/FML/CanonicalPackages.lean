import Langlands.LocalFactor.FML.AgreementProof

/-!
# Canonical FML packages from the Library conductors

Derived Library integration definitions by Worker 455, using the construction
formulas specified by Worker 332 and the published conductor agreements.
They adapt the role of Fukuhiro Ueda's canonical character packages in
epsilon_FML, commit 0b4159be50e1bd45ddff1de4280399576a3e2024 (Apache-2.0).
Modifications: supplied p-adic instances, existing Library conductors instead
of a new choice, and the Library's nontrivial unitary additive-character input.
See CanonicalPackages.md and the retained LICENSE for provenance and scope.
-/

namespace Langlands.FML.Padic

universe u

variable {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
  (T : F.TopologicalData)

/-- Package the same continuous quasicharacter with its existing Library
conductor, certified by the published FML agreement. -/
noncomputable def localQuasiCharData
    (χ : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FML.LocalQuasiCharData F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact
    { character := χ
      conductor := T.multiplicativeConductor χ
      isConductor := (multiplicativeConductorAgreement F T χ _).mpr rfl }

/-- Package the actual circle-to-units transport of a Library additive character
with its existing integer conductor and the published FML certificate. -/
noncomputable def localAddCharData
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    FML.LocalAddCharData F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact
    { character := FML.ofUnitaryAdditiveCharacter ψ
      conductor := T.additiveConductor ψ
      isConductor := (additiveConductorAgreement F T ψ _).mpr rfl }

end Langlands.FML.Padic
