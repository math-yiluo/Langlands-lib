import Langlands.Representation.Exponents.RealCentralBlock
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Actual equivariant retractions onto grouped generalized central spaces. -/

namespace Langlands

universe uG uV

/-- Finite full-central operator span splits every selected group of uniform
generalized central-character spaces by an actual equivariant retraction. -/
def GroupedCentralCharacterRetractionStatement : Prop :=
  ∀ (G : Type uG) [Group G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    Module.Finite ℂ
      (Submodule.span ℂ (Set.range (fun z : Subgroup.center G => ρ (z : G)))) →
    ∀ P : (Subgroup.center G →* ℂˣ) → Prop,
      ∃ r : ρ.IntertwiningMap (groupedCentralCharacterSpace ρ P).toRepresentation,
        (∀ v : groupedCentralCharacterSpace ρ P, r (v : V) = v) ∧
        (∀ (χ : Subgroup.center G →* ℂˣ), ¬ P χ →
          ∀ v : V, v ∈ generalizedCentralCharacterSpace ρ χ → r v = 0)

end Langlands
