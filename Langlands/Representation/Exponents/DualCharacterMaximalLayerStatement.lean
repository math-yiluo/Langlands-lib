import Langlands.Representation.Exponents.DualCharacterQuotient
import Langlands.Representation.Classification.ConstituentRelations

/-! Algebraic maximal layers in a character-detected quotient.
This is a proposition definition, not a proof of the assertion. -/

namespace Langlands

universe uG uH uV

/-- A finite positive exact dual nilpotence order detects a nonzero highest
defect image; every such image has the prescribed scalar central action. -/
def DualCharacterMaximalLayerStatement : Prop :=
  ∀ (G : Type uG) [Group G] (H : Type uH) [CommGroup H]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ι : H →* G)
    (hι : ∀ a, ι a ∈ Subgroup.center G) (χ : H →* ℂˣ)
    (d : ℕ), 0 < d →
      commutativeCharacterNilpotenceIndex (commutativeTranspose (ρ.comp ι)) χ =
        (d : ℕ∞) →
      (∃ a : H,
        Nontrivial (DualCharacterQuotient.defectRangeRepresentation ρ ι hι χ a (d - 1))) ∧
      ∀ a : H,
        Classification.HasScalarCharacter
          (DualCharacterQuotient.defectRangeRepresentation ρ ι hι χ a (d - 1)).ρ ι χ

end Langlands
