import Langlands.BushnellKutzko.SimpleCharacters

/-! # Restriction, twisting and nonemptiness (BK93 (3.2.4)–(3.2.5), (3.3.18), (3.3.21); U3) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- Restriction from the character domain at index `i` to its subgroup at index `j`. -/
noncomputable def simpleCharacterRestriction {F : Type uF} [Field F] [ValuativeRel F]
    {V : Type uV} [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) {i j : ℕ} (hij : i ≤ j)
    (χ : simpleHGroup S.chain S.n S.b q.tail (i + 1) →* ℂˣ) :
    simpleHGroup S.chain S.n S.b q.tail (j + 1) →* ℂˣ :=
  χ.comp (Subgroup.inclusion (simpleHGroup_antitone S.chain S.n S.b q.tail (by omega)))

/-- **BK93 (3.2.4), (3.2.5), (3.3.18), (3.3.21), U3.** The high-index singleton,
restriction images and fibres, the critical-approximation twist, and nonemptiness. -/
def SimpleCharacterRestrictionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    let L := S.chain
    let H := fun m : ℕ => simpleHGroup L S.n S.b q.tail (m + 1)
    let C := simpleCharacters ψF L S.n S.b q.tail
    let r := finiteCriticalDepth L S.n S.b
    let d := (r / 2).toNat
    -- (a)
    (∀ m : ℕ, S.n / 2 ≤ (m : ℤ) → (m : ℤ) < S.n →
      H m = L.unitFiltration (m + 1) ∧ ∃ θ : H m →* ℂˣ, C m = {θ} ∧
        ∀ g : H m, (θ g : ℂ) = elementCharacter (traceCharacter ψF) S.b g) ∧
    -- (b)
    (elementAlgebra S.b ≠ ⊥ → ∀ (m : ℕ) (hm : m ≤ d), (m : ℤ) < S.n →
      let res := simpleCharacterRestriction S q hm
      let X : Set (H m →* ℂˣ) := {χ | simpleCharacterRestriction S q hm χ = 1 ∧
        factorsThroughCentralizerDet S.b χ}
      res '' C m = C d ∧
        ∀ θ ∈ C m, {χ ∈ C m | res χ = res θ} = (fun χ => θ * χ) '' X) ∧
    -- (c)
    (∀ T : Stratum 𝒪[F] F V, S.IsCriticalApproximation T → ∀ q' : T.DefiningSequenceChoice,
      ∀ m : ℕ, r / 2 ≤ (m : ℤ) → (m : ℤ) < r →
        let H' := simpleHGroup T.chain T.n T.b q'.tail (m + 1)
        let C' := simpleCharacters ψF T.chain T.n T.b q'.tail m
        H m = H' ∧ ∃ e : (C m) ≃ C', ∀ θ : C m,
          characterAgreesOn H' (e θ).val θ.val
            (fun g => (elementCharacter (traceCharacter ψF) (S.b - T.b) g)⁻¹)) ∧
    -- (d) and (e)
    (∀ m : ℕ, (m : ℤ) + 1 < S.n →
      (simpleCharacterRestriction S q (Nat.le_succ m)) '' C m = C (m + 1)) ∧
    ∀ m : ℕ, (m : ℤ) < S.n → (C m).Nonempty

end Langlands.BushnellKutzko
