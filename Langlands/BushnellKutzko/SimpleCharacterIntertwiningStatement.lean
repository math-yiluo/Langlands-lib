import Langlands.BushnellKutzko.SimpleCharacters

/-! # Intertwining and normalizer (BK93 (3.3.2), (3.3.17), printed pp. 105, 112; U5) -/

open ValuativeRel
open scoped Pointwise Classical

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

/-- The outer factor `Y` of BK93 (3.3.2), with the scalar convention in U5.
The set of units is computed by translating the specified lattice sum by `1`. -/
def simpleCharacterIntertwiningFactor {F : Type uF} [Field F] [ValuativeRel F]
    {V : Type uV} [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (m : ℕ) : Set (Module.End F V)ˣ :=
  if elementAlgebra S.b = ⊥ then {1} else
    let r := finiteCriticalDepth S.chain S.n S.b
    let N := adjointLattice S.chain S.b (-r)
    let Q := centralizerLattice S.chain S.b (r - (m : ℤ))
    let J := simpleJLayer S.chain S.n S.b q.tail (simpleJCutoff r).toNat
    {g | (g : Module.End F V) - 1 ∈ Q * N ⊔ J}

/-- **BK93 (3.3.2), (3.3.17), U5.** The self-intertwining and normalizer
of each simple character are `Y B_β^× Y` and `Y 𝔎(𝔅_β)`, respectively. -/
def SimpleCharacterIntertwiningStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ m : ℕ, (m : ℤ) < S.n → ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m,
      let Y := simpleCharacterIntertwiningFactor S q m
      let B := centralizerUnitGroup S.b
      let K := relativeOrderNormalizer S.chain S.b
      characterSelfIntertwining θ = Y * (B : Set (Module.End F V)ˣ) * Y ∧
      characterNormalizer θ = Y * (K : Set (Module.End F V)ˣ)

end Langlands.BushnellKutzko
