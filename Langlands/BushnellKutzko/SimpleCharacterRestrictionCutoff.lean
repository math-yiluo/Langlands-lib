import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement

/-! # Restricting a simple character below the cutoff -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A character factors through the relative determinant image if it kills its kernel on
its pullback to the relative endomorphism units. -/
theorem factorsThroughCentralizerDet_iff {β : A} (hE : IsField (elementAlgebra β))
    {H : Subgroup G} (χ : H →* ℂˣ) :
    letI := hE.toField
    let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
    let d := Units.map (LinearMap.det : Module.End (elementAlgebra β) V →* elementAlgebra β)
    factorsThroughCentralizerDet β χ ↔
      ∀ x : H.comap ι, d x = 1 → χ (ι.subgroupComap H x) = 1 := by
  let := hE.toField
  let ι := relativeEndUnits (F := F) (V := V) (elementAlgebra β)
  let d := Units.map (LinearMap.det : Module.End (elementAlgebra β) V →* elementAlgebra β)
  let dH := d.comp (H.comap ι).subtype
  let ρ := χ.comp (ι.subgroupComap H)
  change factorsThroughCentralizerDet β χ ↔ ∀ x : H.comap ι, dH x = 1 → ρ x = 1
  constructor
  · rintro ⟨hE', η, hη⟩ x hx
    have he : dH.rangeRestrict x = 1 := Subtype.ext hx
    have hv := hη x
    change ρ x = η (dH.rangeRestrict x) at hv
    rw [hv, he, map_one]
  · intro h
    have hk : dH.rangeRestrict.ker ≤ ρ.ker := by
      intro x hx
      apply h x
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    refine ⟨hE, dH.rangeRestrict.liftOfSurjective dH.rangeRestrict_surjective ⟨ρ, hk⟩,
      fun x => ?_⟩
    change ρ x = _
    exact (dH.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨ρ, hk⟩ x).symm

/-- Restriction preserves factorization through the relative determinant image. -/
theorem factorsThroughCentralizerDet_restrict {β : A} {H K : Subgroup G} (h : K ≤ H)
    {χ : H →* ℂˣ} (hχ : factorsThroughCentralizerDet β χ) :
    factorsThroughCentralizerDet β (χ.comp (Subgroup.inclusion h)) := by
  have hex := hχ
  obtain ⟨hE, _⟩ := hex
  apply (factorsThroughCentralizerDet_iff hE _).mpr
  intro x hx
  exact (factorsThroughCentralizerDet_iff hE _).mp hχ ⟨x, h x.prop⟩ hx

/-- Multiplication preserves relative determinant factorization. -/
theorem factorsThroughCentralizerDet_mul {β : A} {H : Subgroup G} {χ θ : H →* ℂˣ}
    (hχ : factorsThroughCentralizerDet β χ) (hθ : factorsThroughCentralizerDet β θ) :
    factorsThroughCentralizerDet β (χ * θ) := by
  have h := hχ
  obtain ⟨hE, _⟩ := h
  apply (factorsThroughCentralizerDet_iff hE _).mpr
  intro x hx
  rw [MonoidHom.mul_apply, (factorsThroughCentralizerDet_iff hE _).mp hχ x hx,
    (factorsThroughCentralizerDet_iff hE _).mp hθ x hx, one_mul]

/-- Inversion preserves relative determinant factorization. -/
theorem factorsThroughCentralizerDet_inv {β : A} {H : Subgroup G} {χ : H →* ℂˣ}
    (hχ : factorsThroughCentralizerDet β χ) : factorsThroughCentralizerDet β χ⁻¹ := by
  have h := hχ
  obtain ⟨hE, _⟩ := h
  apply (factorsThroughCentralizerDet_iff hE _).mpr
  intro x hx
  rw [MonoidHom.inv_apply, (factorsThroughCentralizerDet_iff hE _).mp hχ x hx, inv_one]

variable [ValuativeRel F] (L : LatticeChain 𝒪[F] F V) (ψF : AddChar F ℂ) (n : ℤ)

/-- The forward restriction for a terminal simple character follows from the two defining
conditions and the inclusion of domains. -/
theorem simpleCharacters_restrict_nil (β : A) {m j : ℕ} (hmj : m ≤ j)
    {θ : simpleHGroup L n β [] (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L n β [] m) :
    θ.comp (Subgroup.inclusion (simpleHGroup_antitone L n β [] (Nat.succ_le_succ hmj))) ∈
      simpleCharacters ψF L n β [] j := by
  rw [simpleCharacters] at hθ ⊢
  refine ⟨?_, factorsThroughCentralizerDet_restrict _ hθ.2⟩
  intro g hg
  exact hθ.1 _ hg

/-- Below the cutoff a nonterminal simple character restricts to a simple character at any
intermediate index, using normalization of the new domain by the relative order normalizer. -/
theorem simpleCharacters_restrict_cons_of_le_cutoff (β γ : A) (tail : List A) {m j : ℕ}
    (hmj : m ≤ j) (hj : j ≤ (finiteCriticalDepth L n β / 2).toNat)
    (hr : (j : ℤ) < finiteCriticalDepth L n β)
    (hnorm : relativeOrderNormalizer L β ≤ Subgroup.normalizer
      (simpleHGroup L n β (γ :: tail) (j + 1) : Set G))
    {θ : simpleHGroup L n β (γ :: tail) (m + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF L n β (γ :: tail) m) :
    θ.comp (Subgroup.inclusion (simpleHGroup_antitone L n β (γ :: tail) (Nat.succ_le_succ hmj))) ∈
      simpleCharacters ψF L n β (γ :: tail) j := by
  have hm : (m : ℤ) < finiteCriticalDepth L n β := by omega
  have hι := simpleHGroup_antitone L n β (γ :: tail) (Nat.succ_le_succ hmj)
  simp only [simpleCharacters, ite_eq_left hm, ite_eq_left hr] at hθ ⊢
  rw [max_eq_right (hmj.trans hj)] at hθ
  rw [max_eq_right hj]
  obtain ⟨hdet, hθnorm, θ₀, hθ₀, hagree⟩ := hθ
  refine ⟨factorsThroughCentralizerDet_restrict hι hdet, ?_, θ₀, hθ₀, ?_⟩
  · intro g hg
    refine ⟨hnorm hg, ?_⟩
    intro x hx
    exact (hθnorm hg).2 (Subgroup.inclusion hι x) (hι hx)
  · intro g
    obtain ⟨hg, hg₀, hv⟩ := hagree g
    have hg' := simpleHGroup_antitone L n β (γ :: tail) (Nat.succ_le_succ hj) g.prop
    exact ⟨hg', hg₀, hv⟩

end

end Langlands.BushnellKutzko
