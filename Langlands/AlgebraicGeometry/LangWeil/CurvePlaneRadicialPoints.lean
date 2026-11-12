import Mathlib

/-! # Rational points along a radicial map -/

set_option autoImplicit false

universe u v w

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

/-- An injective algebra map whose target becomes `p`-radical over its source after
inverting `s` induces a bijection between the rational points not killing `s`. -/
theorem bijective_comp_of_radicial
    {κ : Type u} {S : Type v} {T : Type w} [Field κ] [CommRing S] [CommRing T]
    [Algebra κ S] [Algebra κ T] (p : ℕ) [ExpChar κ p] [PerfectRing κ p]
    (j : S →ₐ[κ] T) (hj : Function.Injective j) (s : S)
    (hrad : ∀ t : T, ∃ m n : ℕ, ∃ y : S, j y = (j s ^ m * t) ^ p ^ n) :
    Function.Bijective (fun ψ : {ψ : T →ₐ[κ] κ // ψ (j s) ≠ 0} =>
      (⟨ψ.1.comp j, ψ.2⟩ : {χ : S →ₐ[κ] κ // χ s ≠ 0})) := by
  constructor
  · rintro ⟨ψ₁, h₁⟩ ⟨ψ₂, h₂⟩ h
    have hc : ψ₁.comp j = ψ₂.comp j := congrArg Subtype.val h
    have hj' : ∀ x, ψ₁ (j x) = ψ₂ (j x) := fun x => congrArg (fun f => f x) hc
    apply Subtype.ext
    apply AlgHom.ext
    intro t
    obtain ⟨m, n, y, hy⟩ := hrad t
    have h1 := hj' y
    rw [hy, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow, hj' s] at h1
    have h2 := (iterateFrobeniusEquiv κ p n).injective
      (by simpa only [iterateFrobeniusEquiv_apply, iterateFrobenius_def] using h1)
    exact mul_left_cancel₀ (pow_ne_zero m (hj' s ▸ h₁)) h2
  · rintro ⟨χ, hχ⟩
    classical
    let S' := Localization.Away s
    let T' := Localization.Away (j s)
    let j' : S' →+* T' := Localization.awayMap j.toRingHom s
    have hu : IsUnit (χ.toRingHom s) := isUnit_iff_ne_zero.mpr hχ
    let χ' : S' →+* κ := IsLocalization.Away.lift s hu
    have hj'eq : ∀ x : S, j' (algebraMap S S' x) = algebraMap T T' (j x) := fun x =>
      IsLocalization.map_eq _ _
    have hχ'eq : ∀ x : S, χ' (algebraMap S S' x) = χ x := fun x =>
      IsLocalization.Away.lift_eq s hu x
    have : Nontrivial S' := χ'.domain_nontrivial
    have hj'inj : Function.Injective j' := by
      refine Localization.awayMap_injective_iff.mpr fun a ha => ⟨0, ?_⟩
      have : a = 0 := hj (ha.trans (map_zero j).symm)
      simp [this]
    have : Nontrivial T' := hj'inj.nontrivial
    have : ExpChar S' p := expChar_of_injective_algebraMap (algebraMap κ S').injective p
    have : ExpChar T' p := expChar_of_injective_algebraMap (algebraMap κ T').injective p
    have : IsPRadical j' p := by
      refine ⟨fun x => ?_, ?_⟩
      · obtain ⟨k, t, hx⟩ := IsLocalization.Away.surj (j s) x
        obtain ⟨m, n, y, hy⟩ := hrad t
        let v : S' := IsLocalization.Away.invSelf s
        have hw : algebraMap T T' (j s) * j' v = 1 := by
          rw [← hj'eq, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
        refine ⟨n, algebraMap S S' y * v ^ ((m + k) * p ^ n), ?_⟩
        rw [map_mul, map_pow, hj'eq, hy, map_pow, map_mul, map_pow, ← hx]
        calc (algebraMap T T' (j s) ^ m * (x * algebraMap T T' (j s) ^ k)) ^ p ^ n *
              j' v ^ ((m + k) * p ^ n)
            = x ^ p ^ n * (algebraMap T T' (j s) * j' v) ^ ((m + k) * p ^ n) := by ring
          _ = x ^ p ^ n := by rw [hw, one_pow, mul_one]
      · rw [(RingHom.injective_iff_ker_eq_bot j').mp hj'inj]
        exact bot_le
    let ψ' : T' →+* κ := PerfectRing.lift j' χ' p
    have hkey : ∀ x : S, ψ' (algebraMap T T' (j x)) = χ x := by
      intro x
      rw [← hj'eq, PerfectRing.lift_comp_apply, hχ'eq]
    let ψ : T →ₐ[κ] κ :=
      { ψ'.comp (algebraMap T T') with
        commutes' := fun c => by
          change ψ' (algebraMap T T' (algebraMap κ T c)) = algebraMap κ κ c
          rw [← j.commutes, hkey, χ.commutes] }
    have hψ : ∀ x : S, ψ (j x) = χ x := hkey
    refine ⟨⟨ψ, by rw [hψ]; exact hχ⟩, ?_⟩
    apply Subtype.ext
    exact AlgHom.ext hψ

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
