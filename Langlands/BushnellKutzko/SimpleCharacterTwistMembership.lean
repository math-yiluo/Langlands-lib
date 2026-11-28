import Langlands.BushnellKutzko.SimpleCharacterHighExistence
import Langlands.BushnellKutzko.SimpleCharacterTwistRestriction
import Langlands.BushnellKutzko.SimpleCharacterChoiceStatement
import Langlands.BushnellKutzko.SimpleCharacterCovarianceStatement

/-! # Twisted membership from conjugation with trace error -/

open ValuativeRel

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The covariance error for the approximating stratum cancels the error of conjugating
its twist by an element of the centralizer of the original parameter. -/
theorem characterTwist_intertwined_of_covariance (ψF : AddChar F ℂ) (T : Stratum 𝒪[F] F V)
    {β : A} (hβ : β ∈ T.coset) {H H' : Subgroup G} (χ : H →* ℂˣ) (θ : H' →* ℂˣ)
    (hTwist : characterAgreesOn H χ θ (elementCharacter (traceCharacter ψF) (β - T.b)))
    (hCov : ∀ g ∈ T.formalSelfIntertwining, characterConjugationRatio ψF T.b θ g) :
    (centralizerUnitGroup β : Set G) ⊆ characterSelfIntertwining χ := by
  intro g hg x hx
  obtain ⟨_, hx', hval⟩ := hTwist x
  obtain ⟨_, hconj', hconj⟩ := hTwist ⟨g * (x : G) * g⁻¹, hx⟩
  have hg' := T.centralizer_subset_formalSelfIntertwining_of_mem_coset hβ hg
  have he := hCov g hg' ⟨x, hx'⟩ hconj'
  have hcomm : β * (g : A) = (g : A) * β := hg
  have hsum : ((↑g⁻¹ : A) * T.b * (g : A) - T.b) +
      ((↑g⁻¹ : A) * (β - T.b) * (g : A)) = β - T.b := by
    calc
      _ = (↑g⁻¹ : A) * (β * (g : A)) - T.b := by noncomm_ring
      _ = β - T.b := by rw [hcomm, ← mul_assoc, Units.inv_mul, one_mul]
  apply Units.ext
  change (χ ⟨g * (x : G) * g⁻¹, hx⟩ : ℂ) = (χ x : ℂ)
  rw [hconj, he, hval, elementCharacter_conj, mul_assoc, ← elementCharacter_add, hsum]

/-- The reverse membership implication in BK93 (3.3.18) for the successor used in the
recursion, from the covariance identity on the approximating character. -/
theorem simpleCharacters_reverse_twist_of_covariance
    (hDet : IntertwinedUnitCharacterStatement.{uV,uV}) (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) {S T : Stratum 𝒪[F] F V} (hS : S.IsPure)
    (hβ : S.b ∈ T.coset) (tail : List A) (m : ℕ) :
    let L := S.chain
    let r := finiteCriticalDepth L S.n S.b
    let H := simpleHGroup L S.n S.b (T.b :: tail) (m + 1)
    let H' := simpleHGroup L S.n T.b tail (m + 1)
    let C := simpleCharacters ψF L S.n S.b (T.b :: tail) m
    let C' := simpleCharacters ψF L S.n T.b tail m
    (hdiff : S.b - T.b ∈ L.endFiltration (-r)) → (hm : r / 2 ≤ (m : ℤ)) →
    (m : ℤ) < r → (he : H' = H) →
    relativeOrderNormalizer L S.b ≤ Subgroup.normalizer (H : Set G) →
    (∀ θ ∈ C', ∀ g ∈ T.formalSelfIntertwining, characterConjugationRatio ψF T.b θ g) →
    let τ := elementCharacterHom L ψF hψ hdiff (by omega)
      (simpleHGroup_le_unitFiltration L S.n T.b tail (m + 1))
    ∀ θ ∈ C', characterTwistTransport he τ θ ∈ C := by
  intro L r H H' C C' hdiff hm hr he hnorm hCov τ θ hθ
  let χ := characterTwistTransport he τ θ
  have hτ (g : H') : (τ g : ℂ) = elementCharacter (traceCharacter ψF) (S.b - T.b) g := rfl
  have htwist := (characterAgreesOn_iff_eq_twistTransport he τ _ hτ θ χ).mpr rfl
  have hint := characterTwist_intertwined_of_covariance ψF T hβ χ θ htwist (hCov θ hθ)
  have hfactor := factorsThroughCentralizerDet_of_intertwined_simpleHGroup hDet hS (T.b :: tail) χ hint
  have hχnorm : (relativeOrderNormalizer L S.b : Set G) ⊆ characterNormalizer χ :=
    fun _ g => ⟨hnorm g, hint g.1⟩
  change χ ∈ simpleCharacters ψF L S.n S.b (T.b :: tail) m
  change (m : ℤ) < finiteCriticalDepth L S.n S.b at hr
  simp only [simpleCharacters, ite_eq_left hr]
  rw [show max m (r / 2).toNat = m from max_eq_left (by omega)]
  exact ⟨hfactor, hχnorm, θ, hθ, htwist⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem elementCharacter_neg (ψF : AddChar F ℂ) (b : A) (g : G) :
    elementCharacter (traceCharacter ψF) (-b) g =
      (elementCharacter (traceCharacter ψF) b g)⁻¹ := by
  rw [elementCharacter_apply, elementCharacter_apply, neg_mul, AddChar.map_neg_eq_inv]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A twist for an arbitrarily chosen critical approximation follows by composing the
inverse twist to the selected approximation with the twist between approximations. -/
theorem exists_characterTwist_equiv_of_intermediate (ψF : AddChar F ℂ) (β γ δ : A)
    {H H₁ H₂ : Subgroup G} (he₁ : H₁ = H) (he₂ : H₁ = H₂)
    (C : Set (H →* ℂˣ)) (C₁ : Set (H₁ →* ℂˣ)) (C₂ : Set (H₂ →* ℂˣ))
    (τ₁ τ₂ : H₁ →* ℂˣ)
    (hτ₁ : ∀ g : H₁, (τ₁ g : ℂ) = elementCharacter (traceCharacter ψF) (β - γ) g)
    (hτ₂ : ∀ g : H₁, (τ₂ g : ℂ) = elementCharacter (traceCharacter ψF) (δ - γ) g)
    (hC₁ : ∀ θ, θ ∈ C₁ ↔ characterTwistTransport he₁ τ₁ θ ∈ C)
    (hC₂ : C₂ = characterSetTwist H₂ C₁ (elementCharacter (traceCharacter ψF) (δ - γ))) :
    ∃ e : C ≃ C₂, ∀ θ : C, characterAgreesOn H₂ (e θ).val θ.val
      (fun g => (elementCharacter (traceCharacter ψF) (β - δ) g)⁻¹) := by
  let φ₁ := characterTwistTransport he₁ τ₁
  let φ₂ := characterTwistTransport he₂ τ₂
  have h₂ (θ : H₁ →* ℂˣ) : θ ∈ C₁ ↔ φ₂ θ ∈ C₂ := by
    rw [hC₂]
    constructor
    · intro hθ
      exact ⟨θ, hθ, (characterAgreesOn_iff_eq_twistTransport he₂ τ₂ _ hτ₂ θ (φ₂ θ)).mpr rfl⟩
    · rintro ⟨η, hη, ha⟩
      have he := (characterAgreesOn_iff_eq_twistTransport he₂ τ₂ _ hτ₂ η (φ₂ θ)).mp ha
      exact (φ₂.injective he).symm ▸ hη
  let e₁ := Equiv.subtypeEquiv φ₁ hC₁
  let e₂ := Equiv.subtypeEquiv φ₂ h₂
  refine ⟨e₁.symm.trans e₂, fun θ g => ?_⟩
  have h₂g := (characterAgreesOn_iff_eq_twistTransport he₂ τ₂ _ hτ₂
    (e₁.symm θ).val (e₂ (e₁.symm θ)).val).mpr rfl g
  obtain ⟨_, hg₁, hv₂⟩ := h₂g
  have h₁g := characterAgreesOn_twistTransport_symm he₁ τ₁ _ hτ₁ θ.val ⟨g, hg₁⟩
  obtain ⟨_, hg, hv₁⟩ := h₁g
  change ((e₁.symm θ).val ⟨g, hg₁⟩ : ℂ) =
    (θ.val ⟨g, hg⟩ : ℂ) * (elementCharacter (traceCharacter ψF) (β - γ) g)⁻¹ at hv₁
  refine ⟨g.prop, hg, ?_⟩
  change ((e₂ (e₁.symm θ)).val g : ℂ) = _
  rw [hv₂]
  change ((e₁.symm θ).val ⟨g, hg₁⟩ : ℂ) * _ = _
  rw [hv₁, mul_assoc]
  congr 1
  rw [← elementCharacter_neg ψF (β - γ), ← elementCharacter_add,
    show -(β - γ) + (δ - γ) = -(β - δ) by abel, elementCharacter_neg]

end

end Langlands.BushnellKutzko
