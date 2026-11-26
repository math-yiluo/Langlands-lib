import Langlands.BushnellKutzko.SimpleTypesOverCharacter

/-! # The cuspidal cover of simple types over a fixed character (BK94 (3.6)) -/

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko

universe uF uV uσ uΛ uρ

/-- The irreducible cuspidal representations of `GL_f(k_E)` map to the
simple types over a fixed `θ`, compatibly with equivalence and surjectively
up to equivalence. -/
def SimpleTypesOverCharacterCoverStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    1 ≤ Module.finrank F V →
    ∀ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (hS : S.IsSimple),
    S.r = 0 → IsPrincipalOrder S.chain.order →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    let E := elementAlgebra S.b
    letI := hS.1.1.fst.toField
    haveI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    haveI := subfieldIntegers_isDiscreteValuationRing F E
    let 𝓛E := S.chain.subfieldChain E hS.1.1.snd
    let kE := ResidueField (subfieldIntegers F E)
    let f := Module.finrank kE (𝓛E.Layer 0)
    let J := simpleJ S.chain S.n S.b q.tail
    let C := FiniteGeneralLinear.CuspidalRep.{uV, uσ} f kE
    ∃ Λ : C → Rep.{uΛ} ℂ J,
      (∀ σ₀ : C, IsSimpleTypeOver ψF S q θ (Λ σ₀).ρ) ∧
      (∀ σ₀ σ₀' : C, Nonempty (σ₀.obj.ρ.Equiv σ₀'.obj.ρ) →
        Nonempty ((Λ σ₀).ρ.Equiv (Λ σ₀').ρ)) ∧
      (∀ τ : Rep.{uρ} ℂ J, IsSimpleTypeOver ψF S q θ τ.ρ →
        ∃ σ₀ : C, Nonempty (τ.ρ.Equiv (Λ σ₀).ρ))

end Langlands.BushnellKutzko
