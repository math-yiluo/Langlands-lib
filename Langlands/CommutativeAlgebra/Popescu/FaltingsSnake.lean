import Mathlib

/-! # A dimension count from the snake lemma -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open Module

variable {K : Type*} [Field K] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Type u}
  [AddCommGroup X₁] [Module K X₁] [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Z₁] [Module K Z₁]
  [AddCommGroup X₂] [Module K X₂] [AddCommGroup Y₂] [Module K Y₂] [AddCommGroup Z₂] [Module K Z₂]

/-- **Snake dimension count.** Given a map of short exact sequences of vector spaces
`0 → X₁ → Y₁ → Z₁ → 0` to `0 → X₂ → Y₂ → Z₂ → 0` (vertical maps `α`, `β`, `γ`), with `X₁` and
`ker γ` finite-dimensional, `dim X₂ ≤ dim X₁` and `dim coker γ ≤ dim ker γ`, the cokernel of `β`
has dimension at most that of the kernel of `β`. (Indeed `χ(β) = χ(α) + χ(γ)`.) -/
theorem rank_coker_le_rank_ker (i₁ : X₁ →ₗ[K] Y₁) (p₁ : Y₁ →ₗ[K] Z₁) (i₂ : X₂ →ₗ[K] Y₂)
    (p₂ : Y₂ →ₗ[K] Z₂) (hi₁ : Function.Injective i₁) (he₁ : Function.Exact i₁ p₁)
    (hp₁ : Function.Surjective p₁) (hi₂ : Function.Injective i₂) (he₂ : Function.Exact i₂ p₂)
    (hp₂ : Function.Surjective p₂) (α : X₁ →ₗ[K] X₂) (β : Y₁ →ₗ[K] Y₂) (γ : Z₁ →ₗ[K] Z₂)
    (h₁ : β ∘ₗ i₁ = i₂ ∘ₗ α) (h₂ : γ ∘ₗ p₁ = p₂ ∘ₗ β)
    (hX₁ : Module.rank K X₁ < Cardinal.aleph0)
    (hkγ : Module.rank K (LinearMap.ker γ) < Cardinal.aleph0)
    (hX : Module.rank K X₂ ≤ Module.rank K X₁)
    (hγ : Module.rank K (Z₂ ⧸ LinearMap.range γ) ≤ Module.rank K (LinearMap.ker γ)) :
    Module.rank K (Y₂ ⧸ LinearMap.range β) ≤ Module.rank K (LinearMap.ker β) ∧
      Module.rank K (LinearMap.ker β) < Cardinal.aleph0 := by
  have h₁' : ∀ x, β (i₁ x) = i₂ (α x) := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ y, γ (p₁ y) = p₂ (β y) := fun y => LinearMap.congr_fun h₂ y
  -- `V = β⁻¹(X₂)`
  let V : Submodule K Y₁ := Submodule.comap β (LinearMap.range i₂)
  have hVγ : ∀ v : V, p₁ v ∈ LinearMap.ker γ := by
    intro v
    obtain ⟨x, hx⟩ := v.2
    rw [LinearMap.mem_ker, h₂', ← hx]
    exact he₂.apply_apply_eq_zero x
  let f : V →ₗ[K] LinearMap.ker γ :=
    LinearMap.codRestrict (LinearMap.ker γ) (p₁ ∘ₗ V.subtype) hVγ
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := hp₁ z
    have hy : β y ∈ LinearMap.range i₂ := by
      have : p₂ (β y) = 0 := by rw [← h₂']; exact hz
      obtain ⟨x, hx⟩ := (he₂ (β y)).mp this
      exact ⟨x, hx⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hi₁V : LinearMap.range i₁ ≤ V := by
    rintro _ ⟨x, rfl⟩
    exact ⟨α x, (h₁' x).symm⟩
  have hkerf : LinearMap.ker f = (LinearMap.range i₁).comap V.subtype := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hv
      have : p₁ v = 0 := congrArg Subtype.val hv
      obtain ⟨x, hx⟩ := (he₁ (v : Y₁)).mp this
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      apply Subtype.ext
      show p₁ v = 0
      rw [← hx]
      exact he₁.apply_apply_eq_zero x
  have E1 : Module.rank K V = Module.rank K X₁ + Module.rank K (LinearMap.ker γ) := by
    have := LinearMap.rank_range_add_rank_ker f
    rw [LinearMap.range_eq_top.mpr hf, rank_top, hkerf,
      (Submodule.comapSubtypeEquivOfLe hi₁V).rank_eq,
      ← (LinearEquiv.ofInjective i₁ hi₁).rank_eq] at this
    rw [← this, add_comm]
  -- `W = X₂ ∩ β(Y₁)`
  let W : Submodule K Y₂ := LinearMap.range i₂ ⊓ LinearMap.range β
  let g : V →ₗ[K] W := LinearMap.codRestrict W (β ∘ₗ V.subtype) (fun v => ⟨v.2, ⟨v, rfl⟩⟩)
  have hg : Function.Surjective g := by
    rintro ⟨w, hw₁, ⟨y, rfl⟩⟩
    exact ⟨⟨y, hw₁⟩, rfl⟩
  have hkerβV : LinearMap.ker β ≤ V := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    show β y ∈ LinearMap.range i₂
    rw [hy]
    exact zero_mem _
  have hkerg : LinearMap.ker g = (LinearMap.ker β).comap V.subtype := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hv
      exact congrArg Subtype.val hv
    · intro hv
      exact Subtype.ext hv
  have E2 : Module.rank K V = Module.rank K W + Module.rank K (LinearMap.ker β) := by
    have := LinearMap.rank_range_add_rank_ker g
    rw [LinearMap.range_eq_top.mpr hg, rank_top, hkerg,
      (Submodule.comapSubtypeEquivOfLe hkerβV).rank_eq] at this
    rw [← this]
  -- the cokernels
  have hmapQ : LinearMap.range β ≤ (LinearMap.range γ).comap p₂ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨p₁ y, h₂' y⟩
  let q : (Y₂ ⧸ LinearMap.range β) →ₗ[K] (Z₂ ⧸ LinearMap.range γ) :=
    (LinearMap.range β).mapQ (LinearMap.range γ) p₂ hmapQ
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, rfl⟩ := hp₂ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  let h : LinearMap.range i₂ →ₗ[K] (Y₂ ⧸ LinearMap.range β) :=
    (LinearMap.range β).mkQ ∘ₗ (LinearMap.range i₂).subtype
  have hrangeh : LinearMap.range h = LinearMap.ker q := by
    ext c
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ c
    constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩⟩, hx⟩
      rw [LinearMap.mem_ker, ← hx]
      show Submodule.Quotient.mk (p₂ (i₂ x)) = 0
      rw [he₂.apply_apply_eq_zero x]
      rfl
    · intro hy
      have hy' : p₂ y ∈ LinearMap.range γ :=
        (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp hy)
      obtain ⟨z, hz⟩ := hy'
      obtain ⟨y₁, rfl⟩ := hp₁ z
      have : p₂ (y - β y₁) = 0 := by rw [map_sub, ← h₂', hz, sub_self]
      obtain ⟨x, hx⟩ := (he₂ _).mp this
      refine ⟨⟨i₂ x, ⟨x, rfl⟩⟩, ?_⟩
      show Submodule.Quotient.mk (i₂ x) = Submodule.Quotient.mk y
      rw [hx, Submodule.Quotient.eq]
      rw [sub_sub_cancel_left]
      exact neg_mem ⟨y₁, rfl⟩
  have hWle : W ≤ LinearMap.range i₂ := inf_le_left
  have hkerh : LinearMap.ker h = W.comap (LinearMap.range i₂).subtype := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hv
      have : (v : Y₂) ∈ LinearMap.range β := (Submodule.Quotient.mk_eq_zero _).mp hv
      exact ⟨v.2, this⟩
    · intro hv
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv.2
  have E3 : Module.rank K (Y₂ ⧸ LinearMap.range β) =
      Module.rank K (Z₂ ⧸ LinearMap.range γ) + Module.rank K (LinearMap.range h) := by
    have := LinearMap.rank_range_add_rank_ker q
    rw [LinearMap.range_eq_top.mpr hq, rank_top, ← hrangeh] at this
    exact this.symm
  have E4 : Module.rank K X₂ = Module.rank K (LinearMap.range h) + Module.rank K W := by
    have := LinearMap.rank_range_add_rank_ker h
    rw [hkerh, (Submodule.comapSubtypeEquivOfLe hWle).rank_eq,
      ← (LinearEquiv.ofInjective i₂ hi₂).rank_eq] at this
    exact this.symm
  -- cardinal arithmetic
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.mp hX₁
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.mp hkγ
  have hx : Module.rank K X₂ < Cardinal.aleph0 := lt_of_le_of_lt hX hX₁
  obtain ⟨x, hx'⟩ := Cardinal.lt_aleph0.mp hx
  have hVlt : Module.rank K V < Cardinal.aleph0 := by
    rw [E1, ha, hb, ← Nat.cast_add]
    exact Cardinal.natCast_lt_aleph0
  have hWlt : Module.rank K W < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_self_add.trans_eq E2.symm) hVlt
  have hkβlt : Module.rank K (LinearMap.ker β) < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_add_self.trans_eq E2.symm) hVlt
  obtain ⟨w, hw⟩ := Cardinal.lt_aleph0.mp hWlt
  obtain ⟨c, hc⟩ := Cardinal.lt_aleph0.mp hkβlt
  have hrlt : Module.rank K (LinearMap.range h) < Cardinal.aleph0 :=
    lt_of_le_of_lt (le_self_add.trans_eq E4.symm) hx
  obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hrlt
  have helt : Module.rank K (Z₂ ⧸ LinearMap.range γ) < Cardinal.aleph0 := lt_of_le_of_lt hγ hkγ
  obtain ⟨e, he⟩ := Cardinal.lt_aleph0.mp helt
  refine ⟨?_, hkβlt⟩
  have E12 : (a : Cardinal) + b = w + c := by rw [← ha, ← hb, ← hw, ← hc, ← E1, E2]
  have E4' : (x : Cardinal) = r + w := by rw [← hx', ← hr, ← hw, E4]
  have hX' : (x : Cardinal) ≤ a := by rw [← hx', ← ha]; exact hX
  have hγ' : (e : Cardinal) ≤ b := by rw [← he, ← hb]; exact hγ
  rw [E3, he, hr, hc]
  norm_cast at E12 E4' hX' hγ' ⊢
  omega

end Faltings

end Langlands.CommutativeAlgebra.Popescu
