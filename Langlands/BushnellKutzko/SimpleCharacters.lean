import Langlands.BushnellKutzko.SimpleStratumGroups
import Langlands.BushnellKutzko.CharacterIntertwining
import Langlands.BushnellKutzko.AdditiveDual

/-! # Simple characters of a simple stratum (BK93 (3.2.1), (3.2.3), printed pp. 98–99) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uE uV uG

/-- The conductor convention on `ψ_F` of BK93, printed pp. 19–20. -/
def IsBKAdditiveCharacter {F : Type uF} [Field F] [ValuativeRel F] (ψF : AddChar F ℂ) : Prop :=
  (∀ a ∈ 𝓂[F], ψF (a : F) = 1) ∧ ∃ a : 𝒪[F], ψF (a : F) ≠ 1

/-- Agreement of `χ₁` with `χ₂ · twist` on the whole test subgroup `K`.
Membership witnesses record both restriction maps without imposing a choice of
transport between the two domains. -/
def characterAgreesOn {G : Type uG} [Group G] (K : Subgroup G)
    {H₁ H₂ : Subgroup G} (χ₁ : H₁ →* ℂˣ) (χ₂ : H₂ →* ℂˣ) (twist : G → ℂ) : Prop :=
  ∀ g : K, ∃ h₁ : (g : G) ∈ H₁, ∃ h₂ : (g : G) ∈ H₂,
    (χ₁ ⟨g, h₁⟩ : ℂ) = (χ₂ ⟨g, h₂⟩ : ℂ) * twist g

variable {O : Type uO} {F : Type uF} {V : Type uV} [Field F] [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Restriction of scalars on the units of `End_E(V)`. -/
def relativeEndUnits (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V] :
    (Module.End E V)ˣ →* G :=
  Units.map { toFun := LinearMap.restrictScalars F, map_one' := rfl, map_mul' := fun _ _ => rfl }

/-- The restriction of `χ` to `H ∩ B_β^×` factors through the determinant on
`End_{F[β]}(V)`. The factoring character is defined on the determinant image. -/
def factorsThroughCentralizerDet (β : A) {H : Subgroup G} (χ : H →* ℂˣ) : Prop :=
  ∃ hE : IsField (elementAlgebra β),
    letI := hE.toField
    let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
    let U := H.comap ι
    let d := (Units.map (LinearMap.det : Module.End (elementAlgebra β) V →* elementAlgebra β)).comp
      U.subtype
    ∃ η : d.range →* ℂˣ, ∀ x : U, χ ⟨ι x, x.property⟩ = η (d.rangeRestrict x)

variable [CommRing O] [Algebra O F] [Module O V] [IsScalarTower O F V]

open scoped Classical in
/-- `C(𝔄,m,β)` relative to the supplied tail of a defining sequence, as a set
of actual characters of `H^{m+1}(β,𝔄)`. -/
def simpleCharacters (ψF : AddChar F ℂ) (L : LatticeChain O F V) (n : ℤ) :
    (β : A) → (tail : List A) → (m : ℕ) → Set (simpleHGroup L n β tail (m + 1) →* ℂˣ)
  | β, [], m =>
      {θ | (∀ g : simpleHGroup L n β [] (m + 1),
        (g : G) ∈ L.unitFiltration (simpleHCutoff n).toNat →
        (θ g : ℂ) = elementCharacter (traceCharacter ψF) β g) ∧
        factorsThroughCentralizerDet β θ}
  | β, γ :: tail, m =>
      let r := finiteCriticalDepth L n β
      let H := simpleHGroup L n β (γ :: tail) (m + 1)
      if (m : ℤ) < r then
        let j := max m (r / 2).toNat
        {θ | factorsThroughCentralizerDet β θ ∧
          (relativeOrderNormalizer L β : Set G) ⊆ characterNormalizer θ ∧
          ∃ θ₀ ∈ simpleCharacters ψF L n γ tail j,
            characterAgreesOn (simpleHGroup L n β (γ :: tail) (j + 1)) θ θ₀
              (elementCharacter (traceCharacter ψF) (β - γ))}
      else
        {θ | ∃ θ₀ ∈ simpleCharacters ψF L n γ tail m,
          H = simpleHGroup L n γ tail (m + 1) ∧ characterAgreesOn H θ θ₀ (fun _ => 1)}

end Langlands.BushnellKutzko
