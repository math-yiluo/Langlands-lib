import Langlands.BushnellKutzko.BetaExtensionTwist.Intertwining
import Langlands.BushnellKutzko.PairConjugation

/-! # Transport of self-intertwining -/

noncomputable section

namespace Langlands.BushnellKutzko

variable {G H W W' : Type*} [Group G] [Group H]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {J : Subgroup G} {K : Subgroup H}

/-- A self-intertwiner is a nonzero linear map satisfying the conjugation identity. -/
theorem selfIntertwines_iff (ρ : Representation ℂ J W) (x : G) :
    Intertwines ρ ρ x ↔ ∃ f : W →ₗ[ℂ] W, f ≠ 0 ∧
      ∀ (j : J) (hj : x * (j : G) * x⁻¹ ∈ J) (v : W),
        f (ρ ⟨x * (j : G) * x⁻¹, hj⟩ v) = ρ j (f v) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.toLinearMap, fun h => hf (Representation.IntertwiningMap.ext h), ?_⟩
    intro j hj v
    exact Representation.IntertwiningMap.isIntertwining _ _ f ⟨j, hj, j.2⟩ v
  · rintro ⟨f, hf, h⟩
    let T : intertwiningSpace ρ ρ x := ⟨f, fun j => LinearMap.ext fun v =>
      h (intertwiningDomainIncl J J x j) j.2.1 v⟩
    exact ⟨T, fun hT => hf (congrArg Representation.IntertwiningMap.toLinearMap hT)⟩

/-- An equivalence of carrier representations preserves self-intertwining. -/
theorem selfIntertwines_of_equiv {ρ : Representation ℂ J W} {σ : Representation ℂ J W'}
    (e : ρ.Equiv σ) {x : G} (hx : Intertwines ρ ρ x) : Intertwines σ σ x := by
  obtain ⟨f, hf, h⟩ := (selfIntertwines_iff ρ x).1 hx
  let T := e.toLinearMap.comp (f.comp e.symm.toLinearMap)
  refine (selfIntertwines_iff σ x).2 ⟨T, ?_, ?_⟩
  · intro hT
    apply hf
    ext v
    have hz := LinearMap.congr_fun hT (e v)
    change e (f (e.symm (e v))) = 0 at hz
    rw [e.symm_apply_apply] at hz
    change f v = 0
    apply e.toLinearEquiv.injective
    rw [map_zero]
    exact hz
  · intro j hj v
    change e (f (e.symm (σ _ v))) = σ j (e (f (e.symm v)))
    have h₁ := Representation.IntertwiningMap.isIntertwining _ _
      e.symm.toIntertwiningMap ⟨_, hj⟩ v
    have h₂ := Representation.IntertwiningMap.isIntertwining _ _
      e.toIntertwiningMap j (f (e.symm v))
    simp only [Representation.Equiv.coe_toIntertwiningMap] at h₁ h₂
    rw [h₁, h j hj, h₂]

/-- Self-intertwining depends only on the isomorphism class of a subgroup-representation pair. -/
theorem IsPairIsomorphic.selfIntertwining_eq {J' : Subgroup G}
    {ρ : Representation ℂ J W} {σ : Representation ℂ J' W'}
    (h : IsPairIsomorphic ρ σ) :
    representationSelfIntertwining ρ = representationSelfIntertwining σ := by
  obtain ⟨rfl, ⟨e⟩⟩ := h
  have he : ρ.comp (MulEquiv.subgroupCongr (rfl : J = J)).symm.toMonoidHom = ρ := by
    ext j : 1
    rfl
  rw [he] at e
  ext x
  exact ⟨selfIntertwines_of_equiv e, selfIntertwines_of_equiv e.symm⟩

/-- An injective ambient homomorphism preserves the self-intertwining equations when the
subgroup is carried isomorphically onto the target subgroup. -/
theorem selfIntertwines_comp_mulEquiv_iff (φ : G →* H) (hφ : Function.Injective φ)
    (e : J ≃* K) (he : ∀ j : J, (e j : H) = φ (j : G))
    (ρ : Representation ℂ K W) (x : G) :
    Intertwines (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) x ↔
      Intertwines ρ ρ (φ x) := by
  rw [selfIntertwines_iff, selfIntertwines_iff]
  have image_conj (j : J) : φ (x * (j : G) * x⁻¹) = φ x * (e j : H) * (φ x)⁻¹ := by
    simp only [map_mul, map_inv, he]
  have lift_conj (j : J) (hj : φ x * (e j : H) * (φ x)⁻¹ ∈ K) :
      x * (j : G) * x⁻¹ ∈ J := by
    let k : K := ⟨_, hj⟩
    have h : φ (e.symm k : J).val = (k : H) := (he (e.symm k)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply k))
    exact (hφ (h.trans (image_conj j).symm)) ▸ (e.symm k).2
  constructor
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun k hk v => ?_⟩
    obtain ⟨j, rfl⟩ := e.surjective k
    have hj := lift_conj j hk
    have eq : e ⟨_, hj⟩ = ⟨_, hk⟩ := Subtype.ext ((he _).trans (image_conj j))
    have ht := h j hj v
    change f (ρ (e ⟨_, hj⟩) v) = ρ (e j) (f v) at ht
    rwa [eq] at ht
  · rintro ⟨f, hf, h⟩
    refine ⟨f, hf, fun j hj v => ?_⟩
    have hk : φ x * (e j : H) * (φ x)⁻¹ ∈ K := image_conj j ▸ (he ⟨_, hj⟩ ▸ (e ⟨_, hj⟩).2)
    have eq : e ⟨_, hj⟩ = ⟨_, hk⟩ := Subtype.ext ((he _).trans (image_conj j))
    change f (ρ (e ⟨_, hj⟩) v) = ρ (e j) (f v)
    rw [eq]
    exact h (e j) hk v

private theorem selfIntertwines_mul_left (ρ : Representation ℂ J W) (k : J) {x : G}
    (hx : Intertwines ρ ρ x) : Intertwines ρ ρ ((k : G) * x) := by
  obtain ⟨f, hf, h⟩ := (selfIntertwines_iff ρ x).1 hx
  refine (selfIntertwines_iff ρ _).2 ⟨f.comp (ρ k⁻¹), ?_, ?_⟩
  · intro hz
    apply hf
    ext v
    have hz' := LinearMap.congr_fun hz (ρ k v)
    change f (ρ k⁻¹ (ρ k v)) = 0 at hz'
    have hcancel : ρ k⁻¹ (ρ k v) = v := by
      rw [← Module.End.mul_apply (ρ k⁻¹) (ρ k), ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    rwa [hcancel] at hz'
  · intro j hj v
    let a : J := ⟨_, hj⟩
    have eq : (k⁻¹ * a * k : J).val = x * (j : G) * x⁻¹ := by
      change (k : G)⁻¹ * (((k : G) * x) * (j : G) * ((k : G) * x)⁻¹) * k = _
      group
    have hj' := eq ▸ (k⁻¹ * a * k).2
    have e : (k⁻¹ * a : J) = ⟨_, hj'⟩ * k⁻¹ := by
      rw [show (⟨_, hj'⟩ : J) = k⁻¹ * a * k from Subtype.ext eq.symm]
      group
    change f (ρ k⁻¹ (ρ a v)) = ρ j (f (ρ k⁻¹ v))
    rw [← Module.End.mul_apply (ρ k⁻¹) (ρ a), ← map_mul, e, map_mul,
      Module.End.mul_apply, h]

private theorem selfIntertwines_mul_right (ρ : Representation ℂ J W) (k : J) {x : G}
    (hx : Intertwines ρ ρ x) : Intertwines ρ ρ (x * k) := by
  obtain ⟨f, hf, h⟩ := (selfIntertwines_iff ρ x).1 hx
  refine (selfIntertwines_iff ρ _).2 ⟨(ρ k⁻¹).comp f, ?_, ?_⟩
  · intro hz
    apply hf
    ext v
    have hz' := congrArg (ρ k) (LinearMap.congr_fun hz v)
    change ρ k (ρ k⁻¹ (f v)) = ρ k 0 at hz'
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
      map_zero] at hz'
  · intro j hj v
    let a := k * j * k⁻¹
    have eq : x * (a : G) * x⁻¹ = (x * (k : G)) * (j : G) * (x * (k : G))⁻¹ := by
      change x * ((k : G) * (j : G) * (k : G)⁻¹) * x⁻¹ = _
      group
    have hj' := eq.symm ▸ hj
    change ρ k⁻¹ (f (ρ ⟨_, hj⟩ v)) = ρ j (ρ k⁻¹ (f v))
    rw [← show (⟨_, hj'⟩ : J) = ⟨_, hj⟩ from Subtype.ext eq, h a hj' v,
      ← Module.End.mul_apply, ← map_mul, show k⁻¹ * a = j * k⁻¹ by dsimp [a]; group,
      map_mul, Module.End.mul_apply]

/-- A central element self-intertwines every representation with a nonzero carrier. -/
theorem selfIntertwines_of_central (ρ : Representation ℂ J W) [Nontrivial W]
    {x : G} (hx : x ∈ Subgroup.center G) : Intertwines ρ ρ x := by
  refine (selfIntertwines_iff ρ x).2 ⟨LinearMap.id, ?_, ?_⟩
  · intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    exact hv (LinearMap.congr_fun h v)
  · intro j hj v
    have h : x * (j : G) * x⁻¹ = (j : G) :=
      (Subgroup.mem_center_iff.1 hx j).symm ▸ mul_inv_cancel_right _ _
    change ρ ⟨_, hj⟩ v = ρ j v
    rw [show (⟨_, hj⟩ : J) = j from Subtype.ext h]

end Langlands.BushnellKutzko
