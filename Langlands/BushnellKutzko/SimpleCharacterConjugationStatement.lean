import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.ElementFieldInvariants
import Langlands.BushnellKutzko.SplittingBasis

/-! # Transport of simple characters by conjugation -/

open ValuativeRel
open Langlands.Group.RelativeWeyl

namespace Langlands.BushnellKutzko

universe uF uV

/-- Simultaneous conjugation of the order and the stratum transports the
groups and simple characters, and preserves the field invariants. -/
def SimpleCharacterConjugationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V) (m : ℕ), S.r = m → S.IsSimple →
    ∀ g : (Module.End F V)ˣ,
      let f := LinearMap.GeneralLinearGroup.toLinearEquiv g
      let L := S.chain
      let L' := L.linearEquivMap f
      IsHereditaryOrder L'.order ∧
      (L'.order : Set (Module.End F V)) = f.conjRingEquiv '' (L.order : Set (Module.End F V)) ∧
      L'.period = L.period ∧ (L.IsPrincipal → L'.IsPrincipal) ∧
      ∃ T : Stratum 𝒪[F] F V,
        T.chain = L' ∧ T.n = S.n ∧ T.r = S.r ∧ T.b = f.conjRingEquiv S.b ∧ T.IsSimple ∧
        (∀ (q : S.DefiningSequenceChoice) (q' : T.DefiningSequenceChoice) (k : ℕ),
          simpleHGroup L' T.n T.b q'.tail k =
            conjugateSubgroup g (simpleHGroup L S.n S.b q.tail k) ∧
          simpleJGroup L' T.n T.b q'.tail k =
            conjugateSubgroup g (simpleJGroup L S.n S.b q.tail k)) ∧
        simpleCharacterPairs ψF T m =
          (fun P => CharacterPair.conj g⁻¹ P) '' simpleCharacterPairs ψF S m ∧
        elementRamificationIndex F T.b = elementRamificationIndex F S.b ∧
        elementResidueDegree F T.b = elementResidueDegree F S.b

end Langlands.BushnellKutzko
