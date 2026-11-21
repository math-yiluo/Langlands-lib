import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.SubfieldLatticeChain

/-! # Existence and classification of `β`-extensions (BK93 (5.2.2)(i)–(ii), printed p. 166; V2) -/

open ValuativeRel IsLocalRing

namespace Langlands.BushnellKutzko

universe uF uV uW uW₁ uW₂

/-- **BK93 (5.2.2)(i)–(ii), V2.** For a simple stratum `[𝔄, n, 0, β]`, `θ ∈ C(𝔄, 0, β)` and
`η` lying over `θ`: (i) `η` has a `β`-extension; (ii) if `κ` is a `β`-extension of `η`, an
irreducible representation `κ'` of `J(β, 𝔄)` is a `β`-extension of `η` if and only if
`κ' ≅ κ ⊗ ξ` for a character `ξ` of `J(β, 𝔄)`, trivial on `J^1(β, 𝔄)`, that equals
`χ ∘ det_B` on `U(𝔅_β)` for a character `χ` of `k_E^×`. -/
def BetaExtensionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → ∀ hS : S.IsSimple, ∀ q : S.DefiningSequenceChoice,
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) W),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η →
      (∃ (d : ℕ) (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin d → ℂ)),
        IsBetaExtension S.chain S.n S.b q.tail η κ) ∧
      ∀ (W₁ : Type uW₁) [AddCommGroup W₁] [Module ℂ W₁]
        (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) W₁),
        IsBetaExtension S.chain S.n S.b q.tail η κ →
        ∀ (W₂ : Type uW₂) [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]
          (κ' : Representation ℂ (simpleJ S.chain S.n S.b q.tail) W₂),
          IsSmoothRepresentation κ' → κ'.IsIrreducible →
          (IsBetaExtension S.chain S.n S.b q.tail η κ' ↔
            ∃ ξ : simpleJ S.chain S.n S.b q.tail →* ℂˣ,
              (∀ j : simpleJ S.chain S.n S.b q.tail,
                (j : (Module.End F V)ˣ) ∈ simpleJGroup S.chain S.n S.b q.tail 1 → ξ j = 1) ∧
              (letI := hS.1.1.fst.toField;
                haveI : FiniteDimensional F (elementAlgebra S.b) :=
                  S.chain.finiteDimensional_subfield (elementAlgebra S.b);
                haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b);
                ∃ χ : (ResidueField (subfieldIntegers F (elementAlgebra S.b)))ˣ →* ℂˣ,
                  ∀ (x : (Module.End (elementAlgebra S.b) V)ˣ)
                    (hx : relativeEndUnits (elementAlgebra S.b) x ∈
                      relativeUnitFiltration S.chain S.b 0)
                    (a : (subfieldIntegers F (elementAlgebra S.b))ˣ),
                    ((a : subfieldIntegers F (elementAlgebra S.b)) : elementAlgebra S.b) =
                      LinearMap.det (x : Module.End (elementAlgebra S.b) V) →
                    ξ ⟨relativeEndUnits (elementAlgebra S.b) x,
                        relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail hx⟩ =
                      χ (Units.map (residue (subfieldIntegers F (elementAlgebra S.b))) a)) ∧
              Nonempty (Representation.Equiv κ' (κ.tprod (characterRepresentation ξ))))

end Langlands.BushnellKutzko
