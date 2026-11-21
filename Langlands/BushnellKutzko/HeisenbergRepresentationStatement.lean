import Langlands.BushnellKutzko.HeisenbergRepresentation

/-! # Heisenberg representations of a simple character (BK93 (5.1.1), printed p. 158; V1) -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW uW₁ uW₂

/-- **BK93 (5.1.1), V1.** For a simple stratum `[𝔄, n, 0, β]` and `θ ∈ C(𝔄, 0, β)`:
(a) some representation of `J^1(β, 𝔄)` lies over `θ`; (b) any two such are isomorphic;
(c) every `η` lying over `θ` restricts on `H^1(β, 𝔄)` to the scalars `θ(h)`, and
`(dim η)^2 = (J^1 : H^1)`; (d) `I_G(η) = J^1 B_β^× J^1`. -/
def HeisenbergRepresentationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
      (∃ (d : ℕ) (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) (Fin d → ℂ)),
        IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η) ∧
      (∀ (W₁ : Type uW₁) [AddCommGroup W₁] [Module ℂ W₁]
        (W₂ : Type uW₂) [AddCommGroup W₂] [Module ℂ W₂]
        (η₁ : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W₁)
        (η₂ : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W₂),
        IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η₁ →
        IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η₂ →
        Nonempty (Representation.Equiv η₁ η₂)) ∧
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W),
        IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
          (∀ h : simpleHGroup S.chain S.n S.b q.tail 1,
            η (Subgroup.inclusion (simpleHGroup_le_simpleJGroup S.chain S.n S.b q.tail 1) h) =
              (θ h : ℂ) • LinearMap.id) ∧
          Module.finrank ℂ W ^ 2 =
            (simpleHGroup S.chain S.n S.b q.tail 1).relIndex
              (simpleJGroup S.chain S.n S.b q.tail 1) ∧
          representationSelfIntertwining η =
            ((simpleJGroup S.chain S.n S.b q.tail 1 : Set (Module.End F V)ˣ) *
              (centralizerUnitGroup S.b : Set (Module.End F V)ˣ)) *
              (simpleJGroup S.chain S.n S.b q.tail 1 : Set (Module.End F V)ˣ)

end Langlands.BushnellKutzko
