import Langlands.BushnellKutzko.SimpleCharacterPairs
import Langlands.BushnellKutzko.FundamentalStratum

/-! # Residue fields, prime elements and tame corestrictions of a common simple character
(BK94 (5.2), printed p. 132) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Two simple strata `[𝔄,n,0,γ₁]`, `[𝔄,n,0,γ₂]` with the same simple characters have
centralizer orders with the same image in `𝔄/𝔓`, residue fields with the same image in
`𝔄/𝔓`, prime elements congruent modulo `U¹(𝔄)`, and tame corestrictions that agree
modulo one step of the filtration. -/
def SimpleCharacterResidueComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (L : LatticeChain 𝒪[F] F V) (n : ℤ) (S₁ S₂ : SimpleStratumAt L n 0),
      simpleCharacterPairs ψF S₁.1 0 = simpleCharacterPairs ψF S₂.1 0 →
      centralizerLattice L S₁.1.b 0 ⊔ L.endFiltration 1 =
          centralizerLattice L S₂.1.b 0 ⊔ L.endFiltration 1 ∧
      ∀ (h₁ : IsField (elementAlgebra S₁.1.b)) (h₂ : IsField (elementAlgebra S₂.1.b)),
        letI := h₁.toField
        letI := h₂.toField
        (∀ a : subfieldIntegers F (elementAlgebra S₁.1.b),
          ∃ b : subfieldIntegers F (elementAlgebra S₂.1.b),
            subfieldEmbedding F (elementAlgebra S₁.1.b) V a -
              subfieldEmbedding F (elementAlgebra S₂.1.b) V b ∈ L.endFiltration 1) ∧
        (∀ b : subfieldIntegers F (elementAlgebra S₂.1.b),
          ∃ a : subfieldIntegers F (elementAlgebra S₁.1.b),
            subfieldEmbedding F (elementAlgebra S₁.1.b) V a -
              subfieldEmbedding F (elementAlgebra S₂.1.b) V b ∈ L.endFiltration 1) ∧
        (∃ (π₁ : RingPrimeElement (subfieldIntegers F (elementAlgebra S₁.1.b)))
            (π₂ : RingPrimeElement (subfieldIntegers F (elementAlgebra S₂.1.b))),
          ∃ u ∈ L.unitFiltration 1,
            subfieldEmbedding F (elementAlgebra S₂.1.b) V π₂.1 =
              subfieldEmbedding F (elementAlgebra S₁.1.b) V π₁.1 * (u : Module.End F V)) ∧
        ∃ (s₁ : TameCorestriction 𝒪[F] F (elementAlgebra S₁.1.b) V)
          (s₂ : TameCorestriction 𝒪[F] F (elementAlgebra S₂.1.b) V),
          ∀ (k : ℤ), ∀ x ∈ L.endFiltration (-(k + 1)),
            (s₁ x).restrictScalars F - (s₂ x).restrictScalars F ∈ L.endFiltration (-k)

end Langlands.BushnellKutzko
