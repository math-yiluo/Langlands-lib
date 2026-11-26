import Langlands.Representation.Finite.MonomialTrace
import Langlands.BushnellKutzko.PairConjugation

/-! # Conjugation of subgroup–character pairs (BK93 p. 104 and BK94 p. 118) -/

namespace Langlands.BushnellKutzko

universe uG

/-- A subgroup together with a complex character on that subgroup. -/
abbrev CharacterPair (G : Type uG) [Group G] :=
  Langlands.FiniteRep.MonomialTrace.Entry G

namespace CharacterPair

variable {G : Type uG} [Group G]

/-- Conjugation by `x` in the convention `θˣ(h) = θ(x h x⁻¹)`. -/
noncomputable def conj (x : G) (P : CharacterPair G) : CharacterPair G :=
  ⟨_, P.2.comp (conjSubgroupEquiv x⁻¹ P.1).symm.toMonoidHom⟩

/-- Two pairs are conjugate by the subgroup `U` if an element of `U`
conjugates the first pair to the second. -/
def AreConjugateBy (U : Subgroup G) (P Q : CharacterPair G) : Prop :=
  ∃ x : U, P.conj (x : G) = Q

end CharacterPair

end Langlands.BushnellKutzko
