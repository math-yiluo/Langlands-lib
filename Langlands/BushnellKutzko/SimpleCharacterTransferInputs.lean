import Langlands.BushnellKutzko.SimpleCharacterTransferSequences
import Langlands.BushnellKutzko.SimpleCharacterTransferStep
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.SimpleCharacterChoiceStatement

/-! # Subgroup, restriction and choice inputs to simple-character transfer -/

open ValuativeRel
open scoped Pointwise

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

section Transport

variable {G : Type uG} [Group G]

private theorem characterSetTwist_one {H : Subgroup G} (C : Set (H →* ℂˣ)) :
    characterSetTwist H C (fun _ => 1) = C := by
  ext θ
  constructor
  · rintro ⟨χ, hχ, hθ⟩
    have he : θ = χ := by
      apply DFunLike.ext
      intro x
      obtain ⟨_, _, heq⟩ := hθ x
      exact Units.ext (by simpa only [mul_one] using heq)
    exact he.symm ▸ hχ
  · intro hθ
    exact ⟨θ, hθ, fun x => ⟨x.2, x.2, by simp⟩⟩

/-- Untwisted equality of character sets under subgroup transport preserves
existence and uniqueness of agreement. -/
theorem transfer_of_choice {H₁ H₂ H₁' H₂' : Subgroup G}
    {C₁ : Set (H₁ →* ℂˣ)} {C₂ : Set (H₂ →* ℂˣ)}
    {C₁' : Set (H₁' →* ℂˣ)} {C₂' : Set (H₂' →* ℂˣ)}
    (hH₁ : H₁ = H₁') (hH₂ : H₂ = H₂')
    (hC₁ : C₁' = characterSetTwist H₁' C₁ (fun _ => 1))
    (hC₂ : C₂' = characterSetTwist H₂' C₂ (fun _ => 1))
    (h : ∀ θ ∈ C₁', ∃! θ', θ' ∈ C₂' ∧ characterAgreesOn (H₁' ⊓ H₂') θ θ' (fun _ => 1)) :
    ∀ θ ∈ C₁, ∃! θ', θ' ∈ C₂ ∧ characterAgreesOn (H₁ ⊓ H₂) θ θ' (fun _ => 1) := by
  subst H₁'
  subst H₂'
  rw [characterSetTwist_one] at hC₁ hC₂
  simpa only [hC₁, hC₂] using h

private theorem lift_of_inverse_twist {H N : Subgroup G} {C : Set (H →* ℂˣ)}
    {C' : Set (N →* ℂˣ)} {t : G → ℂ} (hH : H = N) (ht : ∀ g, t g ≠ 0)
    (e : C ≃ C') (he : ∀ θ : C, characterAgreesOn N (e θ).val θ.val (fun g => (t g)⁻¹)) :
    ∀ η ∈ C', ∃ θ ∈ C, characterAgreesOn H θ η t := by
  intro η hη
  let θ := e.symm ⟨η, hη⟩
  have h := he θ
  have heta : (e θ).val = η := congrArg Subtype.val (e.apply_symm_apply ⟨η, hη⟩)
  rw [heta] at h
  refine ⟨θ.val, θ.2, fun g => ?_⟩
  have hgN : (g : G) ∈ N := hH ▸ g.2
  obtain ⟨hN, hH', heq⟩ := h ⟨g, hgN⟩
  refine ⟨hH', hN, ?_⟩
  change (θ.val ⟨(g : G), hH'⟩ : ℂ) = (η ⟨(g : G), hN⟩ : ℂ) * t g
  rw [show (η ⟨(g : G), hN⟩ : ℂ) = (θ.val ⟨(g : G), hH'⟩ : ℂ) * (t g)⁻¹ from heq,
    mul_assoc, inv_mul_cancel₀ (ht g), mul_one]

end Transport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- The groups used in transfer have the carrier, generating join and normalizer
supplied by the subgroup properties at index zero. -/
theorem transfer_group_properties (hG : SimpleStratumGroupPropertiesStatement.{uF, uV})
    (S : Stratum 𝒪[F] F V) (h0 : 0 ≤ S.r) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (m : ℕ) (hnonscalar : elementAlgebra S.b ≠ ⊥)
    (hm : (m : ℤ) < finiteCriticalDepth S.chain S.n S.b) :
    let r := finiteCriticalDepth S.chain S.n S.b
    let j := max m (r / 2).toNat
    let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
    let D := simpleHGroup S.chain S.n S.b q.tail (j + 1)
    let U := relativeUnitFiltration S.chain S.b (m + 1)
    let K := relativeOrderNormalizer S.chain S.b
    (∀ {g}, g ∈ H → (g : A) ∈ simpleHLattice S.chain S.n S.b q.tail) ∧
      H = U ⊔ D ∧ K ≤ Subgroup.normalizer (H : Set G) := by
  dsimp only
  let r := finiteCriticalDepth S.chain S.n S.b
  let j := max m (r / 2).toNat
  let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
  let D := simpleHGroup S.chain S.n S.b q.tail (j + 1)
  let U := relativeUnitFiltration S.chain S.b (m + 1)
  let K := relativeOrderNormalizer S.chain S.b
  let S₀ := S.lowerIndex 0 h0
  let q₀ := q.lowerIndex h0
  have h := hG F V S₀ rfl (hS.lowerIndex h0) q₀
  simp only [q₀, S₀, Stratum.lowerIndex] at h
  obtain ⟨hcar, hProd, hNorm, _, _⟩ := h
  refine ⟨?_, ?_, (hNorm (m + 1)).1⟩
  · intro g hg
    have hh : g ∈ simpleHCarrier S.chain S.n S.b q.tail (m + 1) := (hcar (m + 1)).1 ▸ hg
    exact hh.2
  · let c := simpleHCutoff r
    have hc : c.toNat = (r / 2).toNat + 1 := by
      change (m : ℤ) < r at hm
      dsimp [c, simpleHCutoff]
      omega
    by_cases hmc : m + 1 ≤ c.toNat
    · have hci : ((m + 1 : ℕ) : ℤ) ≤ c := by omega
      have hp : (H : Set G) = (U : Set G) *
          (simpleHGroup S.chain S.n S.b q.tail c.toNat : Set G) :=
        (hProd hnonscalar).1 (m + 1) hci
      have hj : j + 1 = c.toNat := by dsimp [j]; omega
      change H = U ⊔ simpleHGroup S.chain S.n S.b q.tail (j + 1)
      rw [hj, Subgroup.sup_eq_closure_mul, ← hp, Subgroup.closure_eq]
    · have hj : j = m := by dsimp [j]; omega
      change H = U ⊔ simpleHGroup S.chain S.n S.b q.tail (j + 1)
      rw [hj]
      exact (sup_eq_right.mpr (relativeUnitFiltration_le_simpleHGroup S.chain S.n S.b q.tail _)).symm

/-- The high critical-twist comparison at a lowered stratum index. -/
theorem transfer_critical_twist (hR : SimpleCharacterRestrictionStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (S T : Stratum 𝒪[F] F V)
    (h0 : 0 ≤ S.r) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (hT : S.IsCriticalApproximation T) (q' : T.DefiningSequenceChoice) (j : ℕ)
    (hj₀ : finiteCriticalDepth S.chain S.n S.b / 2 ≤ (j : ℤ))
    (hj₁ : (j : ℤ) < finiteCriticalDepth S.chain S.n S.b) :
    let H := simpleHGroup S.chain S.n S.b q.tail (j + 1)
    let H' := simpleHGroup T.chain T.n T.b q'.tail (j + 1)
    H = H' ∧ ∀ η ∈ simpleCharacters ψF T.chain T.n T.b q'.tail j,
      ∃ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
        characterAgreesOn H θ η (elementCharacter (traceCharacter ψF) (S.b - T.b)) := by
  let S₀ := S.lowerIndex 0 h0
  let q₀ := q.lowerIndex h0
  have h := (hR F V ψF hψ S₀ rfl (hS.lowerIndex h0) q₀).2.2.1 T hT q' j hj₀ hj₁
  simp only [q₀, S₀, Stratum.lowerIndex] at h
  obtain ⟨heq, e, he⟩ := h
  exact ⟨heq, lift_of_inverse_twist heq (fun g => ((traceCharacter ψF).val_isUnit _).ne_zero) e he⟩

/-- The choice comparison applies at any nonnegative simple stratum index. -/
theorem transfer_choice_comparison (hC : SimpleCharacterChoiceStatement.{uF, uV})
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (S : Stratum 𝒪[F] F V)
    (h0 : 0 ≤ S.r) (hS : S.IsSimple) (q q' : S.DefiningSequenceChoice)
    (m : ℕ) (hm : (m : ℤ) < S.n) :
    let H := simpleHGroup S.chain S.n S.b q.tail (m + 1)
    let H' := simpleHGroup S.chain S.n S.b q'.tail (m + 1)
    H = H' ∧ simpleCharacters ψF S.chain S.n S.b q'.tail m =
      characterSetTwist H' (simpleCharacters ψF S.chain S.n S.b q.tail m) (fun _ => 1) := by
  let S₀ := S.lowerIndex 0 h0
  have h := (hC F V ψF hψ S₀ rfl (hS.lowerIndex h0) (q.lowerIndex h0)).1 (q'.lowerIndex h0) m hm
  dsimp only at h
  rw [q.lowerIndex_tail h0, q'.lowerIndex_tail h0] at h
  exact h

end Langlands.BushnellKutzko
