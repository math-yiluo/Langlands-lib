import Langlands.BushnellKutzko.CharacterPairConjugation
import Langlands.BushnellKutzko.SimpleCharacters

/-! # Simple characters with their domains (BK94 §2, printed p. 118) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "G" => (Module.End F V)ˣ

/-- Simple strata `[𝔄,n,r,β]` on the fixed chain representing `𝔄`. -/
abbrev SimpleStratumAt (L : LatticeChain 𝒪[F] F V) (n r : ℤ) :=
  {S : Stratum 𝒪[F] F V // S.chain = L ∧ S.n = n ∧ S.r = r ∧ S.IsSimple}

/-- `Ĉ(𝔄,m,β)` as actual pairs `(H^{m+1}(β,𝔄), θ)`.
The union ranges over the defining sequences of the simple stratum. -/
def simpleCharacterPairs (ψF : AddChar F ℂ) (S : Stratum 𝒪[F] F V) (m : ℕ) :
    Set (CharacterPair G) :=
  ⋃ q : S.DefiningSequenceChoice,
    (fun θ => (⟨simpleHGroup S.chain S.n S.b q.tail (m + 1), θ⟩ : CharacterPair G)) ''
      simpleCharacters ψF S.chain S.n S.b q.tail m

/-- `S^m_n(𝔄)`, the union of the sets of simple character pairs over the simple
strata on `𝔄` at the specified levels. -/
def simpleCharacterPairsAt (ψF : AddChar F ℂ) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (m : ℕ) : Set (CharacterPair G) :=
  ⋃ S : SimpleStratumAt L n m, simpleCharacterPairs ψF S.1 m

end Langlands.BushnellKutzko
