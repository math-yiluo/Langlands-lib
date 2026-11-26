import Langlands.BushnellKutzko.HeisenbergRepresentation

/-! # Dimension of Heisenberg intertwining spaces (BK93 (5.1.8)) -/

open ValuativeRel
open scoped Classical Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- The Heisenberg representation of a simple character has an intertwining line
at every element of `J^1 B_β^× J^1`, and zero-dimensional intertwining spaces
away from that double-coset product. -/
def HeisenbergIntertwiningDimensionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
      ∀ y : (Module.End F V)ˣ,
        let J₁ : Set (Module.End F V)ˣ := simpleJGroup S.chain S.n S.b q.tail 1
        Module.finrank ℂ (intertwiningSpace η η y) =
          if y ∈ J₁ * (centralizerUnitGroup S.b : Set (Module.End F V)ˣ) * J₁ then 1 else 0

end Langlands.BushnellKutzko
