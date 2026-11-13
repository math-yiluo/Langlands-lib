import Langlands.Sheaf.Renard.HomogeneousOriginStalk
import Langlands.Sheaf.Renard.HomogeneousEquivalenceStatement

/-!
# Proof: the induction sheaf has the coefficients as identity-coset stalk

The natural equivariant identification is `HomogeneousOriginStalk.unitIso`.
-/

namespace Langlands.Sheaf.Renard.HomogeneousEquivalence

/-- Renard III.3.2: the identity-coset stalk of the induction sheaf of a smooth
representation is naturally that representation. -/
theorem originStalk : OriginStalkStatement := by
  intro G _ _ _ _ hG H hH
  exact ⟨(HomogeneousOriginStalk.unitIso hG H hH).symm⟩

end Langlands.Sheaf.Renard.HomogeneousEquivalence
