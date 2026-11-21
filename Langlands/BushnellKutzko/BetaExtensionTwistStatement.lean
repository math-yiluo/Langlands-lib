import Langlands.BushnellKutzko.BetaExtension

/-! # Intertwining of `κ ⊗ ξ` (BK93 (5.3.2), printed p. 176; V3) -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW uW₁ uW₂

/-- **BK93 (5.3.2), V3.** Let `κ` be a `β`-extension of a representation `η` lying over
`θ ∈ C(𝔄, 0, β)`, and `ξ` an irreducible representation of `J(β, 𝔄)` that is trivial on
`J^1(β, 𝔄)`. Then (i) `I_G(κ ⊗ ξ) = J · I_{B^×}(ξ | U(𝔅_β)) · J`; (ii) for `y ∈ B_β^×`,
`I_y(κ ⊗ ξ)` and `I_y(ξ)` have the same dimension; (iii) `κ ⊗ ξ` is irreducible. -/
def BetaExtensionTwistStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
    ∀ (W₁ : Type uW₁) [AddCommGroup W₁] [Module ℂ W₁]
      (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) W₁),
      IsBetaExtension S.chain S.n S.b q.tail η κ →
    ∀ (W₂ : Type uW₂) [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
      (ξ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) W₂), ξ.IsIrreducible →
      (∀ j : simpleJ S.chain S.n S.b q.tail,
        (j : (Module.End F V)ˣ) ∈ simpleJGroup S.chain S.n S.b q.tail 1 → ξ j = 1) →
      representationSelfIntertwining (κ.tprod ξ) =
          ((simpleJ S.chain S.n S.b q.tail : Set (Module.End F V)ˣ) *
            {y | y ∈ centralizerUnitGroup S.b ∧
              y ∈ representationSelfIntertwining
                (ξ.comp (Subgroup.inclusion
                  (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)))}) *
            (simpleJ S.chain S.n S.b q.tail : Set (Module.End F V)ˣ) ∧
        (∀ y ∈ centralizerUnitGroup S.b,
          Module.finrank ℂ (intertwiningSpace (κ.tprod ξ) (κ.tprod ξ) y) =
            Module.finrank ℂ (intertwiningSpace ξ ξ y)) ∧
        (κ.tprod ξ).IsIrreducible

end Langlands.BushnellKutzko
