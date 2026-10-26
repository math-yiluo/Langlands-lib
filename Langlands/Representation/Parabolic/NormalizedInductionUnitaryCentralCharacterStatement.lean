import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Parabolic.LeviCenterRestriction

/-!
# The full unitary central character of actual normalized induction

This closed proposition specifies both existence and the exact character on the
full ambient center. It adds no scalar-action compatibility premise.
-/

namespace Langlands

universe uF uV

/-- Actual normalized upper parabolic induction preserves a supplied smooth
unitary central character by restriction to the full ambient center. -/
def GLNormalizedInductionUnitaryCentralCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (B.Levi F.Carrier) V)
        (c : UnitaryCentralCharacter σ),
        ∃ cI : UnitaryCentralCharacter (T.normalizedParabolicInduced B σ),
          ∀ z : Subgroup.center (GeneralLinear n F.Carrier),
            cI.character z = c.character (B.centerToLeviCenter F.Carrier z)

end Langlands
