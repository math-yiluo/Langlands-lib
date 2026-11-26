import Langlands.BushnellKutzko.HeisenbergCharacterTheory

/-! # Intertwining by the trace of a Heisenberg representation -/

noncomputable section

namespace Langlands.BushnellKutzko.HeisenbergCharacter

universe u v w

variable {G : Type u} [Group G] {H J : Subgroup G} (hHJ : H ≤ J) (χ : H →* ℂˣ)
variable {V : Type v} [AddCommGroup V] [Module ℂ V] {W : Type w} [AddCommGroup W] [Module ℂ W]

/-- The trace of a scalar action is the scalar times the dimension. -/
theorem character_apply_of_scalar [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {c : ℂ}
    (hc : ρ g = c • LinearMap.id) : ρ.character g = c * Module.finrank ℂ V := by
  rw [Representation.character, hc, map_smul, LinearMap.trace_id, smul_eq_mul]

/-- A nonzero vector in a scalar representation gives a copy of the character. -/
theorem contains_of_scalar [Nontrivial V] (ρ : Representation ℂ J V)
    (h : ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (χ a : ℂ) • LinearMap.id) :
    ∃ f : (characterRepresentation χ).IntertwiningMap (ρ.comp (Subgroup.inclusion hHJ)), f ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨⟨LinearMap.toSpanSingleton ℂ V v, fun a => ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro z
    change ((χ a : ℂ) * z) • v = ρ (Subgroup.inclusion hHJ a) (z • v)
    rw [h, LinearMap.smul_apply, LinearMap.id_apply, mul_smul]
  · intro hf
    apply hv
    have he := congrArg (fun f : (characterRepresentation χ).IntertwiningMap
      (ρ.comp (Subgroup.inclusion hHJ)) => f 1) hf
    simpa using he

/-- When two scalar characters agree, their traces at an element and its inverse multiply to
the product of the two representation dimensions. -/
theorem character_mul_inv_of_agreement [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W) (a b : H) (hab : χ a = χ b)
    (hρ : ρ (Subgroup.inclusion hHJ a⁻¹) = (χ a⁻¹ : ℂ) • LinearMap.id)
    (hσ : σ (Subgroup.inclusion hHJ b) = (χ b : ℂ) • LinearMap.id) :
    σ.character (Subgroup.inclusion hHJ b) * ρ.character (Subgroup.inclusion hHJ a⁻¹) =
      ((Module.finrank ℂ W * Module.finrank ℂ V : ℕ) : ℂ) := by
  rw [character_apply_of_scalar σ _ hσ, character_apply_of_scalar ρ _ hρ, map_inv, hab,
    Nat.cast_mul]
  calc
    _ = ((χ b : ℂ) * (↑((χ b)⁻¹) : ℂ)) *
        ((Module.finrank ℂ W : ℂ) * (Module.finrank ℂ V : ℂ)) := by ring
    _ = _ := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- The character product for two scalar extensions gives the dimension of their space of
intertwining maps, multiplied by the relative index of the scalar subgroup. -/
theorem finrank_intertwiningMap_mul_relIndex [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ J V) (σ : Representation ℂ J W) (N : Subgroup J)
    [N.Normal] [N.FiniteIndex] (hNH : N ≤ H.subgroupOf J) (hNρ : N ≤ ρ.ker) (hNσ : N ≤ σ.ker)
    (hρ : ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (χ a : ℂ) • LinearMap.id)
    (hσ : ∀ a : H, σ (Subgroup.inclusion hHJ a) = (χ a : ℂ) • LinearMap.id)
    (htrace : ∀ g : J, (g : G) ∉ H → σ.character g = 0) :
    Module.finrank ℂ (ρ.IntertwiningMap σ) * H.relIndex J =
      Module.finrank ℂ W * Module.finrank ℂ V := by
  apply finrank_intertwiningMap_mul_index ρ σ N hNρ hNσ hNH
  · intro g hg
    let a : H := ⟨(g : G), hg⟩
    have ha : Subgroup.inclusion hHJ a = g := rfl
    rw [← ha, ← map_inv (Subgroup.inclusion hHJ)]
    exact character_mul_inv_of_agreement hHJ χ ρ σ a a rfl (hρ a⁻¹) (hσ a)
  · intro g hg
    rw [htrace g hg, zero_mul]

/-- A finite-dimensional nonzero scalar extension whose character is supported on `H` has the
same ambient self-intertwining set as the scalar character. -/
theorem selfIntertwining_eq [FiniteDimensional ℂ V] [Nontrivial V]
    (ρ : Representation ℂ J V) (N : Subgroup J) [N.Normal] [N.FiniteIndex]
    (hNH : N ≤ H.subgroupOf J) (hNρ : N ≤ ρ.ker)
    (hscalar : ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (χ a : ℂ) • LinearMap.id)
    (htrace : ∀ g : J, (g : G) ∉ H → ρ.character g = 0) :
    representationSelfIntertwining ρ = characterSelfIntertwining χ := by
  ext x
  let K := intertwiningDomain J J x
  let l := intertwiningDomainConj J J x
  let r := intertwiningDomainIncl J J x
  constructor
  · rintro ⟨f, hf⟩ a ha
    have hz : ∃ z, f z ≠ 0 := by
      by_contra! hz
      exact hf (Representation.IntertwiningMap.ext (LinearMap.ext hz))
    obtain ⟨z, hz⟩ := hz
    let k : K := ⟨(a : G), hHJ ha, hHJ a.2⟩
    have e := Representation.IntertwiningMap.isIntertwining _ _ f k z
    change f (ρ (Subgroup.inclusion hHJ (⟨_, ha⟩ : H)) z) =
      ρ (Subgroup.inclusion hHJ a) (f z) at e
    rw [hscalar, hscalar, LinearMap.smul_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.id_apply, map_smul] at e
    exact Units.ext (smul_left_injective ℂ hz e)
  · intro hx
    let D := (intertwiningDomain H H x).subgroupOf K
    let T := N.comap l ⊓ N.comap r
    let : T.Normal := inferInstanceAs ((N.comap l ⊓ N.comap r).Normal)
    let : T.FiniteIndex := inferInstanceAs ((N.comap l ⊓ N.comap r).FiniteIndex)
    have hTD : T ≤ D := fun _ hk => ⟨hNH hk.1, hNH hk.2⟩
    have hTl : T ≤ (ρ.comp l).ker := fun _ hk => hNρ hk.1
    have hTr : T ≤ (ρ.comp r).ker := fun _ hk => hNρ hk.2
    have hinside (g : K) (hg : g ∈ D) :
        Representation.character (ρ.comp r) g * Representation.character (ρ.comp l) g⁻¹ =
          ((Module.finrank ℂ V * Module.finrank ℂ V : ℕ) : ℂ) := by
      let a : H := ⟨x * (g : G) * x⁻¹, hg.1⟩
      let b : H := ⟨(g : G), hg.2⟩
      have ha : l g = Subgroup.inclusion hHJ a := rfl
      have hb : r g = Subgroup.inclusion hHJ b := rfl
      change ρ.character (r g) * ρ.character (l g⁻¹) = _
      rw [map_inv, ha, hb, ← map_inv (Subgroup.inclusion hHJ)]
      exact character_mul_inv_of_agreement hHJ χ ρ ρ a b (hx b hg.1) (hscalar a⁻¹) (hscalar b)
    have houtside (g : K) (hg : g ∉ D) :
        Representation.character (ρ.comp r) g * Representation.character (ρ.comp l) g⁻¹ = 0 := by
      change ρ.character (r g) * ρ.character (l g⁻¹) = 0
      by_cases hrg : (r g : G) ∈ H
      · have hlg : (l g : G) ∉ H := fun h => hg ⟨h, hrg⟩
        rw [htrace (l g⁻¹) (by simpa only [map_inv, Subgroup.coe_inv, Subgroup.inv_mem_iff]
          using hlg), mul_zero]
      · rw [htrace _ hrg, zero_mul]
    have hfin := finrank_intertwiningMap_mul_index (H := D) (ρ.comp l) (ρ.comp r) T hTl hTr
      hTD _ hinside houtside
    have hd : 0 < Module.finrank ℂ V := Module.finrank_pos
    have hf : 0 < Module.finrank ℂ (intertwiningSpace ρ ρ x) := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, zero_mul] at hfin
      exact (Nat.mul_ne_zero hd.ne' hd.ne') hfin.symm
    have : Nontrivial (intertwiningSpace ρ ρ x) := Module.nontrivial_of_finrank_pos hf
    exact exists_ne 0

end Langlands.BushnellKutzko.HeisenbergCharacter
