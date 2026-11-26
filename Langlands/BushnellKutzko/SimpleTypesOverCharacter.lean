import Langlands.BushnellKutzko.SimpleTypes

/-! # Simple types over a fixed simple character (BK94, printed p. 124) -/

open ValuativeRel IsLocalRing

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "G" => (Module.End F V)ˣ
local notation "S₀" => Stratum 𝒪[F] F V

/-- Kind (a) data with the simple character witness specified. The subgroup of `ρ`
is identified with `J(β, 𝔄)` by `IsPairIsomorphic`. -/
def IsSimpleTypeDataOver (ψF : AddChar F ℂ) (S : S₀) (q : S.DefiningSequenceChoice)
    (e : ℕ) (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ)
    {J : Subgroup G} (ρ : Representation ℂ J W) : Prop :=
  IsBKAdditiveCharacter ψF ∧ S.r = 0 ∧ IsPrincipalOrder S.chain.order ∧ ∃ hS : S.IsSimple,
    letI := hS.1.1.fst.toField
    haveI : FiniteDimensional F (elementAlgebra S.b) :=
      S.chain.finiteDimensional_subfield (elementAlgebra S.b)
    haveI := subfieldIntegers_isDiscreteValuationRing F (elementAlgebra S.b)
    let 𝓛E := S.chain.subfieldChain (elementAlgebra S.b) hS.1.1.snd
    let kE := ResidueField (subfieldIntegers F (elementAlgebra S.b))
    let U := relativeUnitFiltration S.chain S.b 0
    e = 𝓛E.period ∧ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail 0 ∧
    ∃ (dη : ℕ) (η : Representation ℂ (simpleJGroup S.chain S.n S.b q.tail 1) (Fin dη → ℂ)),
      IsHeisenbergRepresentation S.chain S.n S.b q.tail θ η ∧
    ∃ (dκ : ℕ) (κ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dκ → ℂ)),
      IsBetaExtension S.chain S.n S.b q.tail η κ ∧
    ∃ (f d : ℕ) (σ₀ : Representation ℂ (GeneralLinear f kE) (Fin d → ℂ)),
      σ₀.IsIrreducible ∧ FiniteGeneralLinear.IsCuspidal σ₀ ∧
    ∃ (b : ∀ i : Fin e, Module.Basis (Fin f) kE (𝓛E.Layer ((i : ℕ) : ℤ)))
      (φ : U →* (Fin e → GeneralLinear f kE)),
      IsLayerReduction 𝓛E U (fun _ hu i _ hv => S.chain.apply_mem_lattice_of_mem_unitFiltration
        hu.2 i hv) b φ ∧
    ∃ (dσ : ℕ) (σ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) (Fin dσ → ℂ)),
      IsSmoothRepresentation σ ∧
      (∀ j : simpleJ S.chain S.n S.b q.tail,
        (j : G) ∈ simpleJGroup S.chain S.n S.b q.tail 1 → σ j = 1) ∧
      Nonempty (Representation.Equiv
        (σ.comp (Subgroup.inclusion (relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail)))
        ((tensorPowerRepresentation σ₀ e).comp φ)) ∧
      IsPairIsomorphic ρ (κ.tprod σ)

/-- Existentially quantifying the character recovers the published kind (a) predicate. -/
theorem isSimpleTypeData_iff_exists_isSimpleTypeDataOver
    (ψF : AddChar F ℂ) (S : S₀) (q : S.DefiningSequenceChoice) (e : ℕ)
    {J : Subgroup G} (ρ : Representation ℂ J W) :
    IsSimpleTypeData ψF S q e ρ ↔ ∃ θ, IsSimpleTypeDataOver ψF S q e θ ρ := by
  constructor
  · rintro ⟨hψ, hr, hprincipal, hS, he, θ, hθ, hdata⟩
    exact ⟨θ, hψ, hr, hprincipal, hS, he, hθ, hdata⟩
  · rintro ⟨θ, hψ, hr, hprincipal, hS, he, hθ, hdata⟩
    exact ⟨hψ, hr, hprincipal, hS, he, θ, hθ, hdata⟩

/-- A representation of `J(β, 𝔄)` is a simple type over `(𝔄, β, θ)` when it has
kind (a) data with the specified simple character of `H^1(β, 𝔄)`. -/
def IsSimpleTypeOver (ψF : AddChar F ℂ) (S : S₀) (q : S.DefiningSequenceChoice)
    (θ : simpleHGroup S.chain S.n S.b q.tail 1 →* ℂˣ)
    (ρ : Representation ℂ (simpleJ S.chain S.n S.b q.tail) W) : Prop :=
  ∃ e : ℕ, IsSimpleTypeDataOver ψF S q e θ ρ

end Langlands.BushnellKutzko
