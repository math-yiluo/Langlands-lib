import Langlands.BushnellKutzko.SimpleCharacterTransferExtension

/-! # Transfer through one common critical approximation -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uG

private theorem characterAgreesOn_apply {G : Type uG} [Group G] {D H N : Subgroup G}
    {χ : H →* ℂˣ} {η : N →* ℂˣ} {t : G → ℂ} (h : characterAgreesOn D χ η t)
    {g : G} (hg : g ∈ D) (hgH : g ∈ H) (hgN : g ∈ N) :
    (χ ⟨g, hgH⟩ : ℂ) = (η ⟨g, hgN⟩ : ℂ) * t g := by
  obtain ⟨_, _, heq⟩ := h ⟨g, hg⟩
  exact heq

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 150000 in
/-- The nonterminal transfer step follows from transfer for the common critical
approximation, the critical twist at the cutoff, and the subgroup properties. -/
theorem simpleCharacterTransfer_cons_of_transfer_next (ψF : AddChar F ℂ)
    (L M : LatticeChain 𝒪[F] F V) (n₁ n₂ : ℤ) (β γ : A)
    (tail₁ tail₂ : List A) (m₁ m₂ : ℕ)
    (hf : IsField (elementAlgebra β))
    (hL : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ L.stabilizer)
    (hM : letI := hf.toField
      ∀ a : (elementAlgebra β)ˣ, subfieldUnits F (elementAlgebra β) V a ∈ M.stabilizer)
    (hm : m₁ / (L.period / elementRamificationIndex F β) =
      m₂ / (M.period / elementRamificationIndex F β)) :
    let r₁ := finiteCriticalDepth L n₁ β
    let r₂ := finiteCriticalDepth M n₂ β
    let j₁ := max m₁ (r₁ / 2).toNat
    let j₂ := max m₂ (r₂ / 2).toNat
    let H₁ := simpleHGroup L n₁ β (γ :: tail₁) (m₁ + 1)
    let H₂ := simpleHGroup M n₂ β (γ :: tail₂) (m₂ + 1)
    let D₁ := simpleHGroup L n₁ β (γ :: tail₁) (j₁ + 1)
    let D₂ := simpleHGroup M n₂ β (γ :: tail₂) (j₂ + 1)
    let N₁ := simpleHGroup L n₁ γ tail₁ (j₁ + 1)
    let N₂ := simpleHGroup M n₂ γ tail₂ (j₂ + 1)
    let C₁ := simpleCharacters ψF L n₁ γ tail₁ j₁
    let C₂ := simpleCharacters ψF M n₂ γ tail₂ j₂
    let K₂ := relativeOrderNormalizer M β
    let U₂ := relativeUnitFiltration M β (m₂ + 1)
    let t := elementCharacter (traceCharacter ψF) (β - γ)
    (m₁ : ℤ) < r₁ → (m₂ : ℤ) < r₂ → (j₂ : ℤ) < r₂ →
    j₁ / (L.period / elementRamificationIndex F β) = j₂ / (M.period / elementRamificationIndex F β) →
    (∀ {g}, g ∈ H₁ → (g : A) ∈ simpleHLattice L n₁ β (γ :: tail₁)) →
    (∀ {g}, g ∈ H₂ → (g : A) ∈ simpleHLattice M n₂ β (γ :: tail₂)) →
    H₂ = U₂ ⊔ D₂ → K₂ ≤ Subgroup.normalizer (H₂ : Set G) →
    D₁ = N₁ → D₂ = N₂ →
    (∀ η ∈ C₂, ∃ χ ∈ simpleCharacters ψF M n₂ β (γ :: tail₂) j₂,
      characterAgreesOn D₂ χ η t) →
    (∀ η₁ ∈ C₁, ∃! η₂, η₂ ∈ C₂ ∧ characterAgreesOn (N₁ ⊓ N₂) η₁ η₂ (fun _ => 1)) →
    ∀ θ₁ ∈ simpleCharacters ψF L n₁ β (γ :: tail₁) m₁,
      ∃! θ₂, θ₂ ∈ simpleCharacters ψF M n₂ β (γ :: tail₂) m₂ ∧
        characterAgreesOn (H₁ ⊓ H₂) θ₁ θ₂ (fun _ => 1) := by
  dsimp only
  let r₁ := finiteCriticalDepth L n₁ β
  let r₂ := finiteCriticalDepth M n₂ β
  let j₁ := max m₁ (r₁ / 2).toNat
  let j₂ := max m₂ (r₂ / 2).toNat
  let H₁ := simpleHGroup L n₁ β (γ :: tail₁) (m₁ + 1)
  let H₂ := simpleHGroup M n₂ β (γ :: tail₂) (m₂ + 1)
  let D₁ := simpleHGroup L n₁ β (γ :: tail₁) (j₁ + 1)
  let D₂ := simpleHGroup M n₂ β (γ :: tail₂) (j₂ + 1)
  let N₁ := simpleHGroup L n₁ γ tail₁ (j₁ + 1)
  let N₂ := simpleHGroup M n₂ γ tail₂ (j₂ + 1)
  let C₁ := simpleCharacters ψF L n₁ γ tail₁ j₁
  let C₂ := simpleCharacters ψF M n₂ γ tail₂ j₂
  let K₂ := relativeOrderNormalizer M β
  let U₂ := relativeUnitFiltration M β (m₂ + 1)
  let t := elementCharacter (traceCharacter ψF) (β - γ)
  intro hm₁ hm₂ hj₂ jnorm hcar₁ hcar₂ hjoin hKH hD₁ hD₂ hLift hNext θ₁ hθ₁
  change (m₁ : ℤ) < r₁ at hm₁
  change (m₂ : ℤ) < r₂ at hm₂
  change (j₂ : ℤ) < r₂ at hj₂
  change H₂ = U₂ ⊔ D₂ at hjoin
  change D₁ = N₁ at hD₁
  change D₂ = N₂ at hD₂
  dsimp only [r₁, r₂, j₂] at hm₁ hm₂ hj₂
  have hθ₁' : factorsThroughCentralizerDet β θ₁ ∧
      ((relativeOrderNormalizer L β : Set G) ⊆ characterNormalizer θ₁) ∧
      ∃ η ∈ C₁, characterAgreesOn D₁ θ₁ η t := by
    rw [simpleCharacters, ite_eq_left hm₁] at hθ₁
    exact hθ₁
  obtain ⟨hθ₁det, _, η₁, hη₁, hθ₁η₁⟩ := hθ₁'
  obtain ⟨η₂, ⟨hη₂, hη⟩, hηuniq⟩ := hNext η₁ hη₁
  obtain ⟨χD, hχD, hχη⟩ := hLift η₂ hη₂
  have hχD' : factorsThroughCentralizerDet β χD ∧ ((K₂ : Set G) ⊆ characterNormalizer χD) := by
    rw [simpleCharacters, ite_eq_left hj₂] at hχD
    exact ⟨hχD.1, hχD.2.1⟩
  have hc₁ : j₁ + 1 = max (m₁ + 1) (simpleHCutoff r₁).toNat := by
    have h₁ : 0 ≤ r₁ := by omega
    have h : (simpleHCutoff r₁).toNat = (r₁ / 2).toNat + 1 := by unfold simpleHCutoff; omega
    rw [h]
    dsimp [j₁]
    omega
  have hc₂ : j₂ + 1 = max (m₂ + 1) (simpleHCutoff r₂).toNat := by
    have h₂ : 0 ≤ r₂ := by omega
    have h : (simpleHCutoff r₂).toNat = (r₂ / 2).toNat + 1 := by unfold simpleHCutoff; omega
    rw [h]
    dsimp [j₂]
    omega
  have hD₁H₁ : D₁ ≤ H₁ := simpleHGroup_antitone L n₁ β (γ :: tail₁) (by rw [hc₁]; exact le_max_left ..)
  have hD₂H₂ : D₂ ≤ H₂ := hjoin.symm ▸ le_sup_right
  have hHigh (g : G) (hg₁ : g ∈ D₁) (hg₂ : g ∈ D₂) :
      ∃ h : g ∈ H₁, θ₁ ⟨g, h⟩ = χD ⟨g, hg₂⟩ := by
    have hgN₁ : g ∈ N₁ := hD₁ ▸ hg₁
    have hgN₂ : g ∈ N₂ := hD₂ ▸ hg₂
    have hv := (characterAgreesOn_inf_iff η₁ η₂).mp hη g hgN₁ hgN₂
    refine ⟨hD₁H₁ hg₁, Units.ext ?_⟩
    rw [characterAgreesOn_apply hθ₁η₁ hg₁ (hD₁H₁ hg₁) hgN₁,
      characterAgreesOn_apply hχη hg₂ hg₂ hgN₂, hv]
  obtain ⟨θ₂, hθ₂det, hθ₂norm, hres, hagree⟩ := exists_agreeing_extension_of_high L M n₁ n₂ β
    (γ :: tail₁) (γ :: tail₂) m₁ m₂ j₁ j₂ hf hL hM hm jnorm hc₁ hc₂ hcar₁ hcar₂
    hjoin hKH θ₁ χD hθ₁det hχD'.1 hχD'.2 hHigh
  have hθ₂η : characterAgreesOn D₂ θ₂ η₂ t := by
    intro g
    obtain ⟨hg, heq⟩ := hres g
    have hn : (g : G) ∈ N₂ := hD₂ ▸ g.2
    exact ⟨hg, hn, (congrArg Units.val heq).trans (characterAgreesOn_apply hχη g.2 g.2 hn)⟩
  have hθ₂ : θ₂ ∈ simpleCharacters ψF M n₂ β (γ :: tail₂) m₂ := by
    rw [simpleCharacters, ite_eq_left hm₂]
    exact ⟨hθ₂det, hθ₂norm, η₂, hη₂, hθ₂η⟩
  refine ⟨θ₂, ⟨hθ₂, hagree⟩, ?_⟩
  rintro θ₂' ⟨hθ₂', hagree'⟩
  have hθ₂'' : factorsThroughCentralizerDet β θ₂' ∧
      ((K₂ : Set G) ⊆ characterNormalizer θ₂') ∧
      ∃ η ∈ C₂, characterAgreesOn D₂ θ₂' η t := by
    rw [simpleCharacters, ite_eq_left hm₂] at hθ₂'
    exact hθ₂'
  obtain ⟨hθ₂det', _, η₂', hη₂', hθ₂η'⟩ := hθ₂''
  have hη' : characterAgreesOn (N₁ ⊓ N₂) η₁ η₂' (fun _ => 1) := by
    apply (characterAgreesOn_inf_iff _ _).mpr
    intro g hg₁ hg₂
    have hgD₁ : g ∈ D₁ := hD₁.symm ▸ hg₁
    have hgD₂ : g ∈ D₂ := hD₂.symm ▸ hg₂
    have h := congrArg Units.val ((characterAgreesOn_inf_iff _ _).mp hagree' g
      (hD₁H₁ hgD₁) (hD₂H₂ hgD₂))
    rw [characterAgreesOn_apply hθ₁η₁ hgD₁ (hD₁H₁ hgD₁) hg₁,
      characterAgreesOn_apply hθ₂η' hgD₂ (hD₂H₂ hgD₂) hg₂] at h
    apply Units.ext
    exact mul_right_cancel₀ ((traceCharacter ψF).val_isUnit _).ne_zero h
  have hηeq : η₂' = η₂ := hηuniq η₂' ⟨hη₂', hη'⟩
  subst η₂'
  have hu : U₂ ≤ H₂ := hjoin.symm ▸ le_sup_left
  apply monoidHom_eq_of_agree_on_generators hjoin hu hD₂H₂ θ₂' θ₂
  · intro u
    exact eq_on_relativeUnitFiltration_of_agreement L M n₁ n₂ β (γ :: tail₁) (γ :: tail₂)
      m₁ m₂ hf hL hM hm hθ₂det' hθ₂det hagree' hagree u u.2
  · intro v
    have hv : (v : G) ∈ N₂ := hD₂ ▸ v.2
    apply Units.ext
    rw [characterAgreesOn_apply hθ₂η' v.2 (hD₂H₂ v.2) hv,
      characterAgreesOn_apply hθ₂η v.2 (hD₂H₂ v.2) hv]

end Langlands.BushnellKutzko
