import Langlands.BaseChange.Norm
import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.Analysis.SpecificLimits.Normed

/-! # A generator of a cyclic algebra is an isometry of the local norm

Let `E` be a nonarchimedean local field which is an algebra over a topological field `F`,
carrying the `F`-module topology, and `σ` an `F`-algebra automorphism of `E` with `σ^l = 1` for
some `l > 0` (for instance a generator of a cyclic algebra). Then `σ` is continuous, hence
preserves the elements `x` with `xⁿ → 0`, i.e. those of norm `< 1`; it therefore preserves the
strict order of norms, and since `σ` has finite order it preserves the norm. See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open Filter Topology

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

omit [IsTopologicalRing F] in
theorem continuous_algEquiv (σ : E ≃ₐ[F] E) : Continuous σ :=
  IsModuleTopology.continuous_of_linearMap (R := F) σ.toLinearEquiv.toLinearMap

theorem norm_lt_one_of_algEquiv (σ : E ≃ₐ[F] E) (x : E) :
    letI := LocalGalois.localNormedField E
    ‖x‖ < 1 → ‖σ x‖ < 1 := by
  let _ := LocalGalois.localNormedField E
  intro hx
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one] at hx ⊢
  have h := ((continuous_algEquiv σ).tendsto 0).comp hx
  rw [map_zero] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, map_pow]

theorem norm_lt_one_iff_algEquiv (σ : E ≃ₐ[F] E) (x : E) :
    letI := LocalGalois.localNormedField E
    ‖σ x‖ < 1 ↔ ‖x‖ < 1 := by
  letI := LocalGalois.localNormedField E
  refine ⟨fun h => ?_, norm_lt_one_of_algEquiv σ x⟩
  have := norm_lt_one_of_algEquiv σ.symm (σ x) h
  rwa [AlgEquiv.symm_apply_apply] at this

theorem norm_lt_norm_iff_algEquiv (σ : E ≃ₐ[F] E) (x : E) {y : E} (hy : y ≠ 0) :
    letI := LocalGalois.localNormedField E
    ‖σ x‖ < ‖σ y‖ ↔ ‖x‖ < ‖y‖ := by
  letI := LocalGalois.localNormedField E
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy
  have h := norm_lt_one_iff_algEquiv σ (x / y)
  rw [map_div₀, norm_div, norm_div, div_lt_one (norm_pos_iff.mpr hσy),
    div_lt_one (norm_pos_iff.mpr hy)] at h
  exact h

/-- **A generator of a cyclic algebra preserves the local norm.** -/
theorem norm_algEquiv_eq {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : σ ^ l = 1) (hl : 0 < l) (x : E) :
    letI := LocalGalois.localNormedField E
    ‖σ x‖ = ‖x‖ := by
  letI := LocalGalois.localNormedField E
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hpow : ∀ k : ℕ, (σ ^ (k + 1)) x = σ ((σ ^ k) x) := fun k => by
    rw [pow_succ', AlgEquiv.mul_apply]
  have hne : ∀ k : ℕ, (σ ^ k) x ≠ 0 := fun k => (map_ne_zero _).mpr hx
  have hl1 : (σ ^ l) x = x := by rw [hσ, AlgEquiv.one_apply]
  rcases lt_trichotomy ‖σ x‖ ‖x‖ with hlt | heq | hgt
  · exfalso
    have hanti : StrictAnti fun k : ℕ => ‖(σ ^ k) x‖ := by
      refine strictAnti_nat_of_succ_lt fun k => ?_
      induction k with
      | zero => simpa using hlt
      | succ k ih =>
        change ‖(σ ^ (k + 1 + 1)) x‖ < ‖(σ ^ (k + 1)) x‖
        rw [hpow (k + 1), hpow k]
        exact (norm_lt_norm_iff_algEquiv σ _ (hne k)).mpr (by rw [← hpow k]; exact ih)
    have := hanti hl
    simp only [hl1, pow_zero, AlgEquiv.one_apply] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have hmono : StrictMono fun k : ℕ => ‖(σ ^ k) x‖ := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      induction k with
      | zero => simpa using hgt
      | succ k ih =>
        change ‖(σ ^ (k + 1)) x‖ < ‖(σ ^ (k + 1 + 1)) x‖
        rw [hpow (k + 1), hpow k]
        have hk1 : (σ ^ (k + 1)) x ≠ 0 := hne (k + 1)
        rw [hpow k] at hk1
        exact (norm_lt_norm_iff_algEquiv σ _ hk1).mpr (by rw [← hpow k]; exact ih)
    have := hmono hl
    simp only [hl1, pow_zero, AlgEquiv.one_apply] at this
    exact lt_irrefl _ this

end Langlands.BaseChange.TwistedLocalDescent
