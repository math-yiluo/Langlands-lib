import Langlands.BushnellKutzko.SimpleCharacters

/-! # Ternary closure of simple character sets -/

namespace Langlands.BushnellKutzko

universe uG uO uF uV

section Characters

variable {G : Type uG} [Group G] {K H H' : Subgroup G}

private theorem characterAgreesOn_div_mul {χ₁ χ₂ χ₃ : H →* ℂˣ} {η₁ η₂ η₃ : H' →* ℂˣ}
    {twist : G → ℂ} (h₁ : characterAgreesOn K χ₁ η₁ twist) (h₂ : characterAgreesOn K χ₂ η₂ twist)
    (h₃ : characterAgreesOn K χ₃ η₃ twist) :
    characterAgreesOn K (χ₁ / χ₂ * χ₃) (η₁ / η₂ * η₃) twist := by
  intro g
  obtain ⟨h, h', heq₁⟩ := h₁ g
  obtain ⟨_, _, heq₂⟩ := h₂ g
  obtain ⟨_, _, heq₃⟩ := h₃ g
  refine ⟨h, h', ?_⟩
  have htwist : twist g ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq₁
    exact Units.ne_zero _ heq₁
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply, Units.val_mul, Units.val_div_eq_div_val]
  rw [heq₁, heq₂, heq₃, mul_div_mul_right _ _ htwist, mul_assoc]

private theorem mem_characterNormalizer_div_mul {χ₁ χ₂ χ₃ : H →* ℂˣ} {a : G}
    (h₁ : a ∈ characterNormalizer χ₁) (h₂ : a ∈ characterNormalizer χ₂)
    (h₃ : a ∈ characterNormalizer χ₃) : a ∈ characterNormalizer (χ₁ / χ₂ * χ₃) := by
  refine ⟨h₁.1, fun g hg => ?_⟩
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply]
  rw [h₁.2 g hg, h₂.2 g hg, h₃.2 g hg]

end Characters

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

set_option maxHeartbeats 800000 in
private theorem factorsThroughCentralizerDet_div_mul {β : A} {H : Subgroup G}
    {χ₁ χ₂ χ₃ : H →* ℂˣ} (h₁ : factorsThroughCentralizerDet β χ₁)
    (h₂ : factorsThroughCentralizerDet β χ₂) (h₃ : factorsThroughCentralizerDet β χ₃) :
    factorsThroughCentralizerDet β (χ₁ / χ₂ * χ₃) := by
  obtain ⟨hE, η₁, hη₁⟩ := h₁
  obtain ⟨hE₂, η₂, hη₂⟩ := h₂
  obtain ⟨hE₃, η₃, hη₃⟩ := h₃
  cases Subsingleton.elim hE₂ hE
  cases Subsingleton.elim hE₃ hE
  refine ⟨hE, η₁ / η₂ * η₃, fun x => ?_⟩
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply]
  rw [hη₁ x, hη₂ x, hη₃ x]

variable {O : Type uO} [CommRing O] [Algebra O F] [Module O V] [IsScalarTower O F V]

/-- Three simple characters on the same defining-sequence domain can be combined as
`χ₁ / χ₂ * χ₃`. The assertion also holds for the extended recursion at high depths. -/
theorem simpleCharacters_div_mul_mem (ψF : AddChar F ℂ) (L : LatticeChain O F V) (n : ℤ)
    (β : A) (tail : List A) (m : ℕ) {χ₁ χ₂ χ₃ : simpleHGroup L n β tail (m + 1) →* ℂˣ}
    (h₁ : χ₁ ∈ simpleCharacters ψF L n β tail m) (h₂ : χ₂ ∈ simpleCharacters ψF L n β tail m)
    (h₃ : χ₃ ∈ simpleCharacters ψF L n β tail m) :
    χ₁ / χ₂ * χ₃ ∈ simpleCharacters ψF L n β tail m := by
  induction tail generalizing β m with
  | nil =>
    refine ⟨fun g hg => ?_, factorsThroughCentralizerDet_div_mul h₁.2 h₂.2 h₃.2⟩
    have heq₁ := h₁.1 g hg
    have heq₂ := h₂.1 g hg
    have heq₃ := h₃.1 g hg
    simp only [MonoidHom.mul_apply, MonoidHom.div_apply, Units.val_mul, Units.val_div_eq_div_val]
    rw [heq₁.trans heq₂.symm, div_self (Units.ne_zero _), one_mul, heq₃]
  | cons γ tail ih =>
    simp only [simpleCharacters] at h₁ h₂ h₃ ⊢
    by_cases hmr : (m : ℤ) < finiteCriticalDepth L n β
    · rw [ite_eq_left hmr] at h₁ h₂ h₃ ⊢
      obtain ⟨hdet₁, hnorm₁, η₁, hη₁, ha₁⟩ := h₁
      obtain ⟨hdet₂, hnorm₂, η₂, hη₂, ha₂⟩ := h₂
      obtain ⟨hdet₃, hnorm₃, η₃, hη₃, ha₃⟩ := h₃
      exact ⟨factorsThroughCentralizerDet_div_mul hdet₁ hdet₂ hdet₃,
        fun _ h => mem_characterNormalizer_div_mul (hnorm₁ h) (hnorm₂ h) (hnorm₃ h),
        η₁ / η₂ * η₃, ih γ _ hη₁ hη₂ hη₃, characterAgreesOn_div_mul ha₁ ha₂ ha₃⟩
    · rw [ite_eq_right hmr] at h₁ h₂ h₃ ⊢
      obtain ⟨η₁, hη₁, hdom, ha₁⟩ := h₁
      obtain ⟨η₂, hη₂, _, ha₂⟩ := h₂
      obtain ⟨η₃, hη₃, _, ha₃⟩ := h₃
      exact ⟨η₁ / η₂ * η₃, ih γ _ hη₁ hη₂ hη₃, hdom, characterAgreesOn_div_mul ha₁ ha₂ ha₃⟩

end Langlands.BushnellKutzko
