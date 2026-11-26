import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement

/-! # Conjugation of simple characters with their additive trace factor -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Conjugation changes the values of `θ` by the element character of the
conjugation difference of `β`, on the intersection of the two domains. -/
def characterConjugationRatio (ψF : AddChar F ℂ) (β : A) {H : Subgroup G}
    (θ : H →* ℂˣ) (g : G) : Prop :=
  ∀ (h : H) (hh : g * (h : G) * g⁻¹ ∈ H),
    (θ ⟨_, hh⟩ : ℂ) = (θ h : ℂ) *
      elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * β * (g : A) - β) (h : G)

/-- The conjugation formula of BK93 (3.3.9) for the character at the successor
parameter. The shallower index `t` can be supplied independently. -/
def SimpleCharacterCovarianceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    ∀ m t : ℕ, (m : ℤ) < S.n → (t : ℤ) < S.n →
    ((m : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b →
    ((t : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b → t / 2 ≤ m →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail m,
      let Y := simpleCharacterIntertwiningFactor S q t
      ∀ g ∈ Y * (centralizerUnitGroup S.b : Set (Module.End F V)ˣ) * Y,
        characterConjugationRatio ψF S.b θ g

/-- Pulling back an element character along conjugation conjugates its coefficient
in the opposite direction. -/
theorem elementCharacter_conj (ψF : AddChar F ℂ) (β : A) (g h : G) :
    elementCharacter (traceCharacter ψF) β (g * h * g⁻¹) =
      elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * β * (g : A)) h := by
  have heq : (↑(g * h * g⁻¹) : A) - 1 = (g : A) * ((h : A) - 1) * (↑g⁻¹ : A) := by
    simp only [Units.val_mul, mul_sub, mul_one, sub_mul, Units.mul_inv]
  simp only [elementCharacter_apply, traceCharacter_apply, heq]
  congr 1
  calc
    LinearMap.trace F V (β * ((g : A) * ((h : A) - 1) * (↑g⁻¹ : A))) =
        LinearMap.trace F V ((β * (g : A)) * ((h : A) - 1) * (↑g⁻¹ : A)) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [LinearMap.trace_mul_cycle]
      simp only [mul_assoc]

theorem elementCharacter_add (ψF : AddChar F ℂ) (β γ : A) (h : G) :
    elementCharacter (traceCharacter ψF) (β + γ) h =
      elementCharacter (traceCharacter ψF) β h * elementCharacter (traceCharacter ψF) γ h := by
  simp only [elementCharacter_apply, add_mul, AddChar.map_add_eq_mul]

/-- The additive trace factor for a product splits along the two conjugations. -/
theorem elementCharacter_conjugationDifference_mul (ψF : AddChar F ℂ) (β : A) (g x h : G) :
    elementCharacter (traceCharacter ψF) ((↑(g * x)⁻¹ : A) * β * (↑(g * x) : A) - β) h =
      elementCharacter (traceCharacter ψF) ((↑x⁻¹ : A) * β * (x : A) - β) h *
        elementCharacter (traceCharacter ψF) ((↑g⁻¹ : A) * β * (g : A) - β) (x * h * x⁻¹) := by
  rw [elementCharacter_conj ψF _ x h]
  simp only [elementCharacter_apply, ← AddChar.map_add_eq_mul, ← add_mul]
  congr 2
  simp only [mul_inv_rev, Units.val_mul, mul_sub, sub_mul, mul_assoc]
  abel

/-- Two conjugation formulas compose if the intermediate conjugate belongs to the domain. -/
theorem characterConjugationRatio.mul_of_overlap (ψF : AddChar F ℂ) (β : A) {H : Subgroup G}
    (θ : H →* ℂˣ) {g x : G} (hg : characterConjugationRatio ψF β θ g)
    (hx : characterConjugationRatio ψF β θ x)
    (hmid : ∀ h : H, (g * x) * (h : G) * (g * x)⁻¹ ∈ H → x * (h : G) * x⁻¹ ∈ H) :
    characterConjugationRatio ψF β θ (g * x) := by
  intro h hh
  have hconj : g * (x * (h : G) * x⁻¹) * g⁻¹ = (g * x) * (h : G) * (g * x)⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  let k : H := ⟨_, hmid h hh⟩
  have hk : g * (k : G) * g⁻¹ ∈ H := hconj.symm ▸ hh
  have heq : (⟨_, hh⟩ : H) = ⟨_, hk⟩ := Subtype.ext hconj.symm
  rw [heq, hg k hk, hx h (hmid h hh), elementCharacter_conjugationDifference_mul, mul_assoc]

/-- Twisting the character by an element character adds its coefficient to the
conjugation formula. -/
theorem characterConjugationRatio.of_twist (ψF : AddChar F ℂ) {β c : A} {H : Subgroup G}
    {θ θ₀ : H →* ℂˣ} {g : G} (h₀ : characterConjugationRatio ψF β θ₀ g)
    (htwist : ∀ h : H, (θ h : ℂ) = (θ₀ h : ℂ) * elementCharacter (traceCharacter ψF) c (h : G)) :
    characterConjugationRatio ψF (β + c) θ g := by
  intro h hh
  let e : A → ℂ := fun b => elementCharacter (traceCharacter ψF) b (h : G)
  have hc : e ((↑g⁻¹ : A) * c * (g : A)) = e c * e ((↑g⁻¹ : A) * c * (g : A) - c) := by
    rw [← elementCharacter_add]
    congr 1
    abel
  have heq : (↑g⁻¹ : A) * (β + c) * (g : A) - (β + c) =
      ((↑g⁻¹ : A) * β * (g : A) - β) + ((↑g⁻¹ : A) * c * (g : A) - c) := by
    rw [mul_add, add_mul]
    abel
  rw [htwist, h₀ h hh, htwist, elementCharacter_conj, heq, elementCharacter_add]
  change (θ₀ h : ℂ) * e _ * e ((↑g⁻¹ : A) * c * (g : A)) =
    ((θ₀ h : ℂ) * e c) * (e _ * e ((↑g⁻¹ : A) * c * (g : A) - c))
  rw [hc]
  ring

end Langlands.BushnellKutzko
