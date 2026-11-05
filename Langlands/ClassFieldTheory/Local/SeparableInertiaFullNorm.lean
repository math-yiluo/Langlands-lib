import Langlands.ClassFieldTheory.Local.SeparableInertiaFullNormPrimePower

/-! # Full norm surjectivity under separable inertia valuation hypotheses -/

noncomputable section

open Module
open scoped NNReal

namespace Langlands.ClassFieldTheory.Local.SeparableInertiaNorm

namespace ReductionHyp

variable {E M : Type*} [Field E] [Field M] [Algebra E M]
  [FiniteDimensional E M] [IsGalois E M]
  {w : Valuation M ℝ≥0} {p : ℕ} (h : ReductionHyp (E := E) w p)

include h

/-- Full norm surjectivity for an arbitrary finite Galois group. -/
theorem surjective_unit_norm :
    Function.Surjective (Units.map (Algebra.norm E : M →* E)) := by
  classical
  let N := (Units.map (Algebra.norm E : M →* E)).range
  let Q := Eˣ ⧸ N
  let f : Eˣ →* Q := QuotientGroup.mk' N
  have hsylow : ∀ (q : ℕ), q.Prime → ∀ u : Eˣ,
      ∃ m : ℕ, ¬ q ∣ m ∧ f u ^ m = 1 := by
    intro q hq u
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (finrank_pos (R := E) (M := M)).ne' q hq.ne_one
    have hcard : Nat.card Gal(M/E) = finrank E M := IsGalois.card_aut_eq_finrank E M
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q (n := a)
      (by rw [hcard, hN]; exact dvd_mul_right _ _)
    set B := IntermediateField.fixedField H
    have hBM : finrank B M = q ^ a := by
      rw [IntermediateField.finrank_fixedField_eq_card, hH]
    have hEB : finrank E B = m := by
      have := Module.finrank_mul_finrank E B M
      rw [hBM, hN, mul_comm] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos a) this
    obtain ⟨z, hz⟩ := h.surjective_norm_pgroup hq a B hBM (algebraMap E B (u : E))
    have hz0 : z ≠ 0 := by
      apply (Algebra.norm_ne_zero_iff (R := B)).mp
      rw [hz]
      exact (map_ne_zero_iff _ (algebraMap E B).injective).mpr u.ne_zero
    refine ⟨m, hm, ?_⟩
    rw [← map_pow]
    change (QuotientGroup.mk' N) (u ^ m) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨Units.mk0 z hz0, ?_⟩
    apply Units.ext
    change Algebra.norm E z = (u : E) ^ m
    rw [← Algebra.norm_norm (S := B), hz, Algebra.norm_algebraMap, hEB]
  intro u
  have hord : orderOf (f u) = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨m, hqm, hm⟩ := hsylow q hq u
    exact hqm (hqd.trans (orderOf_dvd_of_pow_eq_one hm))
  have hu : f u = 1 := orderOf_eq_one_iff.mp hord
  exact (QuotientGroup.eq_one_iff u).mp hu

/-- Full field norm surjectivity, including zero. -/
theorem surjective_norm : Function.Surjective (Algebra.norm E : M → E) := by
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, Algebra.norm_zero⟩
  obtain ⟨x, hx⟩ := h.surjective_unit_norm (Units.mk0 u hu)
  exact ⟨x, congrArg Units.val hx⟩

end ReductionHyp

namespace AmbientHyp

variable {U Ω : Type*} [Field U] [Field Ω] [Algebra U Ω] [IsGalois U Ω]
  {w : Valuation Ω ℝ≥0} (h : AmbientHyp (U := U) w)

include h

/-- A finite Galois subextension of a finite extension of the ambient base satisfies
all the reduction hypotheses for a suitable residue-characteristic prime. -/
theorem exists_reductionHyp {E M : Type*} [Field E] [Field M]
    [Algebra U E] [Algebra E Ω] [IsScalarTower U E Ω] [FiniteDimensional U E]
    [Algebra E M] [Algebra M Ω] [IsScalarTower E M Ω]
    [FiniteDimensional E M] [IsGalois E M] :
    ∃ p : ℕ, ReductionHyp (E := E) (w.comap (algebraMap M Ω)) p := by
  have hEΩ : IsGalois E Ω := IsGalois.tower_top_of_isGalois U E Ω
  have hMΩ : IsGalois M Ω := IsGalois.tower_top_of_isGalois E M Ω
  have hcomp : (w.comap (algebraMap M Ω)).comap (algebraMap E M) =
      w.comap (algebraMap E Ω) := by
    rw [← Valuation.comap_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨p, hp, hpm⟩ := exists_prime_natCast (w.comap (algebraMap M Ω))
  obtain ⟨ϖ, hϖ⟩ := h.unif
  refine ⟨p, fun σ x => ?_, hp, hpm, ?_, ?_, fun x hx => ?_, ?_, ?_⟩
  · simp only [Valuation.comap_apply]
    rw [← AlgEquiv.liftNormal_commutes σ Ω x, h.inv_of]
  · exact valHensel_comap h.hensel (fun σ x => h.inv_of (σ.restrictScalars E) x)
      fun x hx => (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx
  · rw [hcomp]
    exact valResidueRoot_comap h.residueRoot h.res
  · obtain ⟨c, hc1, hc2⟩ := h.res (algebraMap M Ω x) hx
    refine ⟨algebraMap U E c, ?_, ?_⟩
    · simp only [Valuation.comap_apply]
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    · simp only [Valuation.comap_apply]
      rwa [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · refine ⟨finrank E M * finrank U E, Nat.mul_pos finrank_pos finrank_pos,
      (w.comap (algebraMap U Ω)) ϖ, hϖ.1, hϖ.2.1, fun x hx0 hx1 => ?_⟩
    have hc : w (algebraMap U Ω (Algebra.norm U (Algebra.norm E x))) =
        (w.comap (algebraMap M Ω)) x ^ (finrank E M * finrank U E) := by
      rw [val_norm_eq h.inv, val_norm_eq (fun σ y => h.inv_of σ y) x, pow_mul]
      rfl
    have hc0 : Algebra.norm U (Algebra.norm E x) ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff, Algebra.norm_eq_zero_iff]
      exact hx0
    have hc1 : (w.comap (algebraMap U Ω)) (Algebra.norm U (Algebra.norm E x)) ≤ 1 := by
      rw [Valuation.comap_apply, hc]
      exact pow_le_one₀ zero_le hx1
    obtain ⟨k, hk⟩ := hϖ.2.2 _ hc0 hc1
    exact ⟨k, by rw [← hc, ← hk]; rfl⟩
  · refine ⟨algebraMap U E ϖ, ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact hϖ.1
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      exact hϖ.2.1

/-- The full unit norm is surjective for finite Galois extensions inside the ambient
field, over any finite extension of its base. -/
theorem surjective_unit_norm {E M : Type*} [Field E] [Field M]
    [Algebra U E] [Algebra E Ω] [IsScalarTower U E Ω] [FiniteDimensional U E]
    [Algebra E M] [Algebra M Ω] [IsScalarTower E M Ω]
    [FiniteDimensional E M] [IsGalois E M] :
    Function.Surjective (Units.map (Algebra.norm E : M →* E)) := by
  obtain ⟨p, hp⟩ := h.exists_reductionHyp (E := E) (M := M)
  exact hp.surjective_unit_norm

/-- A chosen norm preimage for every unit in a finite Galois subextension. -/
def unitNormSection {E M : Type*} [Field E] [Field M]
    [Algebra U E] [Algebra E Ω] [IsScalarTower U E Ω] [FiniteDimensional U E]
    [Algebra E M] [Algebra M Ω] [IsScalarTower E M Ω]
    [FiniteDimensional E M] [IsGalois E M] : Eˣ → Mˣ :=
  fun u => Classical.choose (h.surjective_unit_norm (E := E) (M := M) u)

/-- The chosen unit norm preimages satisfy the determinant norm equation. -/
theorem norm_unitNormSection {E M : Type*} [Field E] [Field M]
    [Algebra U E] [Algebra E Ω] [IsScalarTower U E Ω] [FiniteDimensional U E]
    [Algebra E M] [Algebra M Ω] [IsScalarTower E M Ω]
    [FiniteDimensional E M] [IsGalois E M] (u : Eˣ) :
    Units.map (Algebra.norm E : M →* E) (h.unitNormSection (M := M) u) = u :=
  Classical.choose_spec (h.surjective_unit_norm (E := E) (M := M) u)

end AmbientHyp

end Langlands.ClassFieldTheory.Local.SeparableInertiaNorm
