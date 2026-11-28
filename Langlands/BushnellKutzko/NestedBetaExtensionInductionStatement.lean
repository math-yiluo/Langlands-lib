import Langlands.BushnellKutzko.BetaExtension
import Mathlib.RepresentationTheory.Coinduced

/-! # Transporting a `β`-extension along nested orders (BK93 (5.2.5), existence) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uW₁ uW₂ uX

/-- **BK93 (5.2.5), existence, for nested orders.** Let `[𝔄₁, n₁, 0, β]` and `[𝔄₂, n₂, 0, β]` be
simple strata with the same element `β`, every lattice of the chain of `𝔄₁` being a lattice of
the chain of `𝔄₂`. Let `θᵢ ∈ C(𝔄ᵢ, 0, β)` agree on `H¹(β, 𝔄₁) ∩ H¹(β, 𝔄₂)`, let `ηᵢ` be
representations of `J¹(β, 𝔄ᵢ)` over `θᵢ`, and let `κ₁` be a `β`-extension of `η₁`. Then `η₂`
extends to a representation `κ₂` of `J(β, 𝔄₂)` on the space of `η₂` such that, in
`Γ = U(𝔅₂) U¹(𝔄₂)`, the representation induced from the restriction of `κ₁` to `U(𝔅₂) J¹(β, 𝔄₁)`
is equivalent to the representation induced from `κ₂`. -/
def NestedBetaExtensionInductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S₁ S₂ : Stratum 𝒪[F] F V), S₂.b = S₁.b → S₁.r = 0 → S₂.r = 0 →
      S₁.IsSimple → S₂.IsSimple → (∀ i : ℤ, ∃ j : ℤ, S₂.chain.lattice j = S₁.chain.lattice i) →
    ∀ (q₁ : S₁.DefiningSequenceChoice) (q₂ : S₂.DefiningSequenceChoice),
    ∀ θ₁ ∈ simpleCharacters ψF S₁.chain S₁.n S₁.b q₁.tail 0,
    ∀ θ₂ ∈ simpleCharacters ψF S₂.chain S₂.n S₂.b q₂.tail 0,
      characterAgreesOn (simpleHGroup S₁.chain S₁.n S₁.b q₁.tail 1 ⊓
        simpleHGroup S₂.chain S₂.n S₂.b q₂.tail 1) θ₁ θ₂ (fun _ => 1) →
    ∀ (W₁ : Type uW₁) [AddCommGroup W₁] [Module ℂ W₁]
      (η₁ : Representation ℂ (simpleJGroup S₁.chain S₁.n S₁.b q₁.tail 1) W₁),
      IsHeisenbergRepresentation S₁.chain S₁.n S₁.b q₁.tail θ₁ η₁ →
    ∀ (W₂ : Type uW₂) [AddCommGroup W₂] [Module ℂ W₂]
      (η₂ : Representation ℂ (simpleJGroup S₂.chain S₂.n S₂.b q₂.tail 1) W₂),
      IsHeisenbergRepresentation S₂.chain S₂.n S₂.b q₂.tail θ₂ η₂ →
    ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X]
      (κ₁ : Representation ℂ (simpleJ S₁.chain S₁.n S₁.b q₁.tail) X),
      IsBetaExtension S₁.chain S₁.n S₁.b q₁.tail η₁ κ₁ →
    ∃ κ₂ : Representation ℂ (simpleJ S₂.chain S₂.n S₂.b q₂.tail) W₂,
      κ₂.comp (Subgroup.inclusion (simpleJGroup_one_le_simpleJ S₂.chain S₂.n S₂.b q₂.tail)) =
        η₂ ∧
      ∀ (hPJ : relativeUnitFiltration S₂.chain S₁.b 0 ⊔ simpleJGroup S₁.chain S₁.n S₁.b q₁.tail 1
          ≤ simpleJ S₁.chain S₁.n S₁.b q₁.tail)
        (hPΓ : relativeUnitFiltration S₂.chain S₁.b 0 ⊔ simpleJGroup S₁.chain S₁.n S₁.b q₁.tail 1
          ≤ relativeUnitFiltration S₂.chain S₁.b 0 ⊔ S₂.chain.unitFiltration 1)
        (hJΓ : simpleJ S₂.chain S₂.n S₂.b q₂.tail ≤
          relativeUnitFiltration S₂.chain S₁.b 0 ⊔ S₂.chain.unitFiltration 1),
        Nonempty (Representation.Equiv
          (Representation.coind ((relativeUnitFiltration S₂.chain S₁.b 0 ⊔
              simpleJGroup S₁.chain S₁.n S₁.b q₁.tail 1).subgroupOf
            (relativeUnitFiltration S₂.chain S₁.b 0 ⊔ S₂.chain.unitFiltration 1)).subtype
            ((κ₁.comp (Subgroup.inclusion hPJ)).comp
              (Subgroup.subgroupOfEquivOfLe hPΓ).toMonoidHom))
          (Representation.coind ((simpleJ S₂.chain S₂.n S₂.b q₂.tail).subgroupOf
            (relativeUnitFiltration S₂.chain S₁.b 0 ⊔ S₂.chain.unitFiltration 1)).subtype
            (κ₂.comp (Subgroup.subgroupOfEquivOfLe hJΓ).toMonoidHom)))

end Langlands.BushnellKutzko
