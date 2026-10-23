import Langlands.LocalFactor.FML.Conductors
import Langlands.HarmonicAnalysis.Conductor

/-!
# Agreement of FML and Library conductor conventions

Derived comparison statements by Worker 40, using the published adaptation of
Fukuhiro Ueda's epsilon_FML at commit 0b4159be50e1bd45ddff1de4280399576a3e2024.
These propositions compare the actual definitions with the same supplied
local-field instances. See AgreementStatement.md for source correspondence
and LICENSE for the retained Apache-2.0 license of the adapted definitions.
-/

namespace Langlands.FML.Padic

universe u

/-- The FML lattice at depth `-n` and the Library additive lattice at level `n`
have the same underlying set, for every supplied p-adic field structure. -/
def LatticeAgreementStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ n : ℤ,
      (FML.lattice F.Carrier (-n) : Set F.Carrier) =
        (T.additiveLattice n : Set F.Carrier)

/-- The actual unit subgroups agree at every natural-number depth, including zero. -/
def UnitFiltrationAgreementStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ k : ℕ, FML.unitFiltration F.Carrier k = T.principalUnits k

/-- The exact FML conductor of the transported nontrivial unitary character is
the Library's existing integer conductor. -/
def AdditiveConductorAgreementStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier) (n : ℤ),
      FML.IsAdditiveConductor F.Carrier (FML.ofUnitaryAdditiveCharacter ψ) n ↔
        n = T.additiveConductor ψ

/-- The exact FML conductor of the same continuous quasicharacter is the
Library's existing natural-number conductor. -/
def MultiplicativeConductorAgreementStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : Langlands.PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier) (m : ℕ),
      FML.IsMultiplicativeConductor F.Carrier χ m ↔ m = T.multiplicativeConductor χ

end Langlands.FML.Padic
