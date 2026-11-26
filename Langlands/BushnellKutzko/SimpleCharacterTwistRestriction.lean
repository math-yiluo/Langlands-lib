import Langlands.BushnellKutzko.SimpleCharacterCore
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.SimpleIntertwiningProof
import Langlands.BushnellKutzko.SimpleCharacterIntertwiningStatement

/-! # Twisting and adjacent restriction -/

open ValuativeRel
open scoped Pointwise Classical

namespace Langlands.BushnellKutzko

noncomputable section

universe uF uV uG

section Transport

variable {G : Type uG} [Group G] {H K : Subgroup G}

/-- Multiplication by a character followed by transport to an equal subgroup. -/
def characterTwistTransport (h : H = K) (τ : H →* ℂˣ) : (H →* ℂˣ) ≃ (K →* ℂˣ) where
  toFun χ := (χ * τ).comp (MulEquiv.subgroupCongr h).symm.toMonoidHom
  invFun ξ := ξ.comp (MulEquiv.subgroupCongr h).toMonoidHom * τ⁻¹
  left_inv χ := by
    ext g
    simp [mul_assoc]
  right_inv ξ := by
    ext g
    simp [mul_assoc]

@[simp]
theorem characterTwistTransport_apply (h : H = K) (τ χ : H →* ℂˣ) (x : K) :
    characterTwistTransport h τ χ x = (χ * τ) ((MulEquiv.subgroupCongr h).symm x) := rfl

@[simp]
theorem characterTwistTransport_symm_apply (h : H = K) (τ : H →* ℂˣ) (ξ : K →* ℂˣ) (x : H) :
    (characterTwistTransport h τ).symm ξ x = ξ (MulEquiv.subgroupCongr h x) * (τ x)⁻¹ := rfl

/-- Pointwise twisted agreement on the entire domain identifies the unique transported
character. -/
theorem characterAgreesOn_iff_eq_twistTransport (h : H = K) (τ : H →* ℂˣ)
    (ψ : G → ℂ) (hτ : ∀ x : H, (τ x : ℂ) = ψ x) (χ : H →* ℂˣ) (ξ : K →* ℂˣ) :
    characterAgreesOn K ξ χ ψ ↔ ξ = characterTwistTransport h τ χ := by
  subst K
  constructor
  · intro hagree
    ext x
    obtain ⟨_, _, hx⟩ := hagree x
    change (ξ x : ℂ) = (χ x : ℂ) * (τ x : ℂ)
    simpa only [hτ] using hx
  · intro he
    subst ξ
    intro x
    refine ⟨x.prop, x.prop, ?_⟩
    change (χ x : ℂ) * (τ x : ℂ) = (χ x : ℂ) * ψ x
    rw [hτ]

/-- The inverse of the twist equivalence is pointwise multiplication by the inverse twist. -/
theorem characterAgreesOn_twistTransport_symm (h : H = K) (τ : H →* ℂˣ)
    (ψ : G → ℂ) (hτ : ∀ x : H, (τ x : ℂ) = ψ x) (ξ : K →* ℂˣ) :
    characterAgreesOn H ((characterTwistTransport h τ).symm ξ) ξ (fun x => (ψ x)⁻¹) := by
  subst K
  intro x
  refine ⟨x.prop, x.prop, ?_⟩
  change ((ξ x * (τ x)⁻¹ : ℂˣ) : ℂ) = (ξ x : ℂ) * (ψ x)⁻¹
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, hτ]

private theorem image_eq_of_mem_equiv {A B : Type*} (e : A ≃ B) (s : Set A) (t : Set B)
    (h : ∀ a, a ∈ s ↔ e a ∈ t) : e '' s = t := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (h a).mp ha
  · intro hb
    exact ⟨e.symm b, (h _).mpr (by simpa using hb), e.apply_symm_apply b⟩

/-- Compatible twists on two subgroup levels transport the image under restriction. -/
theorem restriction_image_eq_of_twistTransport {D E : Subgroup G}
    (hH : H = K) (hD : D = E) (hDH : D ≤ H) (hEK : E ≤ K) (τ : H →* ℂˣ)
    (C : Set (H →* ℂˣ)) (C' : Set (K →* ℂˣ))
    (Cdeeper : Set (D →* ℂˣ)) (Cdeeper' : Set (E →* ℂˣ))
    (hC : ∀ χ, χ ∈ C ↔ characterTwistTransport hH τ χ ∈ C')
    (hCdeeper : ∀ χ, χ ∈ Cdeeper ↔
      characterTwistTransport hD (τ.comp (Subgroup.inclusion hDH)) χ ∈ Cdeeper')
    (hImage : (fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion hDH)) '' C = Cdeeper) :
    (fun χ : K →* ℂˣ => χ.comp (Subgroup.inclusion hEK)) '' C' = Cdeeper' := by
  let e := characterTwistTransport hH τ
  let f := characterTwistTransport hD (τ.comp (Subgroup.inclusion hDH))
  let res := fun χ : H →* ℂˣ => χ.comp (Subgroup.inclusion hDH)
  let res' := fun χ : K →* ℂˣ => χ.comp (Subgroup.inclusion hEK)
  have hcomp : res' ∘ e = f ∘ res := by
    funext χ
    apply MonoidHom.ext
    intro x
    rfl
  calc
    res' '' C' = res' '' (e '' C) := congrArg (Set.image res') (image_eq_of_mem_equiv e C C' hC).symm
    _ = (res' ∘ e) '' C := Set.image_image res' e C
    _ = (f ∘ res) '' C := congrArg (fun g => g '' C) hcomp
    _ = f '' (res '' C) := (Set.image_image f res C).symm
    _ = f '' Cdeeper := congrArg (Set.image f) hImage
    _ = Cdeeper' := image_eq_of_mem_equiv f Cdeeper Cdeeper' hCdeeper

end Transport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Once the domains agree, the defining condition gives the forward twist, and beyond
critical depth the perturbation is already trivial. -/
theorem simpleCharacters_twist_cons_iff_of_reverse (L : LatticeChain 𝒪[F] F V)
    (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF) (n : ℤ) (β γ : A) (tail : List A)
    (m : ℕ) :
    let r := finiteCriticalDepth L n β
    let H := simpleHGroup L n β (γ :: tail) (m + 1)
    let H' := simpleHGroup L n γ tail (m + 1)
    let C := simpleCharacters ψF L n β (γ :: tail) m
    let C' := simpleCharacters ψF L n γ tail m
    (hdiff : β - γ ∈ L.endFiltration (-r)) → (hm : r / 2 ≤ (m : ℤ)) → (he : H' = H) →
    let τ := elementCharacterHom L ψF hψ hdiff
      (by omega)
      (simpleHGroup_le_unitFiltration L n γ tail (m + 1))
    let e := characterTwistTransport he τ
    ((m : ℤ) < r → ∀ η ∈ C', e η ∈ C) →
    ∀ η, η ∈ C' ↔ e η ∈ C := by
  intro r H H' C C' hdiff hm he τ e hreverse η
  have hτ (x : H') : (τ x : ℂ) = elementCharacter (traceCharacter ψF) (β - γ) x := rfl
  have hmax : max m (r / 2).toNat = m := max_eq_left (by omega)
  by_cases hr : (m : ℤ) < finiteCriticalDepth L n β
  · refine ⟨hreverse hr η, ?_⟩
    intro hη
    change e η ∈ simpleCharacters ψF L n β (γ :: tail) m at hη
    simp only [simpleCharacters, ite_eq_left hr] at hη
    rw [hmax] at hη
    obtain ⟨_, _, θ, hθ, ha⟩ := hη
    have hθe := (characterAgreesOn_iff_eq_twistTransport he τ _ hτ θ (e η)).mp ha
    have hEq : η = θ := e.injective hθe
    exact hEq.symm ▸ hθ
  · have htrivial (x : H') : elementCharacter (traceCharacter ψF) (β - γ) x = 1 := by
      exact elementCharacter_eq_one_of_depth L ψF hψ hdiff
        (by dsimp [r]; omega)
        (simpleHGroup_le_unitFiltration L n γ tail (m + 1) x.prop)
    have hadd (x : H') : (τ x : ℂ) = 1 := (hτ x).trans (htrivial x)
    change η ∈ C' ↔ e η ∈ simpleCharacters ψF L n β (γ :: tail) m
    simp only [simpleCharacters, ite_eq_right hr]
    constructor
    · intro hη
      exact ⟨η, hη, he.symm,
        (characterAgreesOn_iff_eq_twistTransport he τ _ hadd η (e η)).mpr rfl⟩
    · rintro ⟨θ, hθ, _, ha⟩
      have hθe := (characterAgreesOn_iff_eq_twistTransport he τ _ hadd θ (e η)).mp ha
      have hEq : η = θ := e.injective hθe
      exact hEq.symm ▸ hθ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A centralizer element of any point of a stratum coset formally intertwines that stratum. -/
theorem Stratum.centralizer_subset_formalSelfIntertwining_of_mem_coset (T : Stratum 𝒪[F] F V)
    {β : A} (hβ : β ∈ T.coset) :
    (centralizerUnitGroup β : Set G) ⊆ T.formalSelfIntertwining := by
  intro g hg
  refine ⟨β, hβ, ?_⟩
  change β * (g : A) = (g : A) * β at hg
  rwa [mul_assoc, hg, ← mul_assoc, Units.inv_mul, one_mul]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleIntertwiningNeighborhood_subset_characterFactor
    (T T₀ : Stratum 𝒪[F] F V) (q : T₀.DefiningSequenceChoice) (ht : 0 ≤ T.r)
    (hchain : T₀.chain = T.chain) (hn : T₀.n = T.n) (hb₀ : T₀.b = T.b) :
    T.simpleIntertwiningNeighborhood ⊆ simpleCharacterIntertwiningFactor T₀ q T.r.toNat := by
  intro g hg
  by_cases hb : elementAlgebra T.b = ⊥
  · have hc : criticalExponent T.chain T.b = ⊥ := by simp [criticalExponent, hb]
    simpa [simpleCharacterIntertwiningFactor, hb₀, hb, Stratum.simpleIntertwiningNeighborhood,
      hc] using hg
  · have hc : criticalExponent T.chain T.b ≠ ⊥ := by simp [criticalExponent, hb]
    rcases hg with ⟨h, _⟩ | ⟨k, hk, hg⟩
    · exact (hc h).elim
    · have hr := finiteCriticalDepth_of_criticalExponent_eq T.chain T.n (-k) T.b
        (by simpa only [neg_neg] using hk)
      simp only [simpleCharacterIntertwiningFactor, hchain, hn, hb₀, ite_eq_right hb, hr, neg_neg,
        Set.mem_ofPred_eq, Int.toNat_of_nonneg ht]
      apply Submodule.mem_sup_left
      have hd : -(T.r + k) = -k - T.r := by omega
      simpa only [hd] using hg

/-- All formal intertwiners at the supplied depth belong to the double coset in the
character covariance formula at that depth. -/
theorem formalSelfIntertwining_subset_characterDoubleCoset
    (T T₀ : Stratum 𝒪[F] F V) (hS : T.IsSimple) (q : T₀.DefiningSequenceChoice) (ht : 0 ≤ T.r)
    (hchain : T₀.chain = T.chain) (hn : T₀.n = T.n) (hb : T₀.b = T.b) :
    let Y := simpleCharacterIntertwiningFactor T₀ q T.r.toNat
    T.formalSelfIntertwining ⊆ Y * (centralizerUnitGroup T₀.b : Set G) * Y := by
  intro Y
  let := T.chain.finiteDimensional
  rw [simpleIntertwining F V T hS, hb]
  have h := simpleIntertwiningNeighborhood_subset_characterFactor T T₀ q ht hchain hn hb
  exact Set.mul_subset_mul (Set.mul_subset_mul h (fun _ hg => hg)) h

end

end Langlands.BushnellKutzko
