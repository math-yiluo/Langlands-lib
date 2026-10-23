import Langlands.LocalFactor.FML.Valuation
import Langlands.LocalFactor.FML.Characters
import Langlands.LocalField.Normalization.Definitions

/-!
# Exact conductor predicates and supplied p-adic instances

Adapted by Worker 20 from Fukuhiro Ueda, epsilon_FML, commit
0b4159be50e1bd45ddff1de4280399576a3e2024 (Apache-2.0).
Modifications: project namespace and imports; only conductor predicates and
packages, plus explicit specialization to the Library's supplied local fields.
See Conductors.md and LICENSE for provenance and the retained license.
-/

namespace Langlands.FML

open scoped WithZero

universe u

section Conductors

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Triviality on the entire lattice of depth `r`. -/
def AddCharTrivialOnLattice (ψ : ContinuousAddChar F) (r : ℤ) : Prop :=
  ∀ x : F, x ∈ lattice F r → ψ x = 1

/-- Triviality on the entire unit-filtration subgroup at depth `m`. -/
def QuasiCharTrivialOnUnitFiltration (χ : ContinuousQuasiChar F) (m : ℕ) : Prop :=
  ∀ x : Fˣ, x ∈ unitFiltration F m → χ x = 1

/-- The least triviality depth is `-n`, in the additive-conductor convention. -/
def IsAdditiveConductor (ψ : ContinuousAddChar F) (n : ℤ) : Prop :=
  AddCharTrivialOnLattice F ψ (-n) ∧
    ∀ r : ℤ, AddCharTrivialOnLattice F ψ r → -n ≤ r

/-- The least natural-number triviality depth of a quasicharacter. -/
def IsMultiplicativeConductor (χ : ContinuousQuasiChar F) (m : ℕ) : Prop :=
  QuasiCharTrivialOnUnitFiltration F χ m ∧
    ∀ r : ℕ, QuasiCharTrivialOnUnitFiltration F χ r → m ≤ r

/-- A supplied additive character and an exact conductor certificate. -/
structure LocalAddCharData where
  character : ContinuousAddChar F
  conductor : ℤ
  isConductor : IsAdditiveConductor F character conductor

/-- A supplied quasicharacter and an exact conductor certificate. -/
structure LocalQuasiCharData where
  character : ContinuousQuasiChar F
  conductor : ℕ
  isConductor : IsMultiplicativeConductor F character conductor

end Conductors

namespace Padic

variable {p : ℕ} [Fact p.Prime] {F : Langlands.PadicField.{u} p}
  (T : F.TopologicalData)

/-- The generic normalized multiplicative valuation instantiated by this `T`. -/
noncomputable abbrev normalizedValuation : Valuation F.Carrier ℤᵐ⁰ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  normalizedMultiplicativeValuation F.Carrier

/-- Both constructors use the identical value-group map. -/
theorem normalizedValuation_eq_discreteValuation :
    normalizedValuation T = T.discreteValuation := rfl

/-- The additive valuation for this supplied local-field structure. -/
noncomputable abbrev ord : AddValuation F.Carrier (WithTop ℤ) :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  FML.ord F.Carrier

/-- The generic lattice with exactly the instances supplied by `T`. -/
noncomputable abbrev lattice (n : ℤ) : Submodule T.Integers F.Carrier :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  FML.lattice F.Carrier n

/-- The generic unit filtration with exactly the instances supplied by `T`. -/
noncomputable abbrev unitFiltration (n : ℕ) : Subgroup F.Carrierˣ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  FML.unitFiltration F.Carrier n

/-- The required character transport with exactly the topology supplied by `T`. -/
noncomputable abbrev ofUnitaryAdditiveCharacter
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    @ContinuousAddChar F.Carrier _ T.topology :=
  letI := T.topology
  FML.ofUnitaryAdditiveCharacter ψ

end Padic

end Langlands.FML
