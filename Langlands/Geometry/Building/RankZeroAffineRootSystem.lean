import Langlands.Geometry.Building.AffineWeylGroups

/-! # Affine root systems admitting rank zero

This module preserves the derivative-spanning AR 1 variant and its reviewed
proofs separately from the affine-spanning predicate in `AffineRootSystem`.
-/

noncomputable section

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- `Ψ ⊆ A*` is an affine root system (KP Definition 1.3.1):

* AR 1: `Φ = ∇Ψ` spans `V*`, `Ψ` consists of non-constant functionals, and `Φ` is finite.
  KP print "`Ψ` spans `A*`"; the derivative form is the one that admits KP's rank-zero system
  `Ψ = ∅` on a point, and it is equivalent to KP's for nonempty `Ψ`
  (`IsAffineRootSystemWithRankZero.span_eq_top` in `RankZeroAffineRootSystem`);
* AR 2: every `ψ ∈ Ψ` has a coroot vector `ψ̇∨ ∈ V` (`IsCoroot`);
* AR 3: `ψ̇(η̇∨) ∈ ℤ` for all `ψ, η ∈ Ψ`;
* AR 4 (as corrected in 2024): for each `a ∈ Φ`, `{ψ ∈ Ψ | ψ̇ = a}` is infinite and has no
  accumulation point; the latter is stated as: for each `ψ ∈ Ψ` and `M`, only finitely many
  `η ∈ Ψ` with `η̇ = ψ̇` satisfy `|η - ψ| ≤ M`. -/
structure IsAffineRootSystemWithRankZero (Ψ : Set (A →ᵃ[ℝ] ℝ)) : Prop where
  span_derivativeRoots_eq_top : Submodule.span ℝ (derivativeRoots Ψ) = ⊤
  linear_ne_zero : ∀ ψ ∈ Ψ, ψ.linear ≠ 0
  finite_derivativeRoots : (derivativeRoots Ψ).Finite
  exists_isCoroot : ∀ ψ ∈ Ψ, ∃ v : V, IsCoroot Ψ ψ v
  coroot_integral : ∀ ψ ∈ Ψ, ∀ η ∈ Ψ, ∀ v : V, IsCoroot Ψ η v → ∃ n : ℤ, ψ.linear v = n
  infinite_fiber : ∀ ψ ∈ Ψ, {η | η ∈ Ψ ∧ η.linear = ψ.linear}.Infinite
  finite_bounded : ∀ ψ ∈ Ψ, ∀ M : ℝ,
    {η | η ∈ Ψ ∧ η.linear = ψ.linear ∧ ∀ x : A, |η x - ψ x| ≤ M}.Finite

/-- An affine root system is stable under negation (AR 2 applied to `ψ` itself). -/
theorem IsAffineRootSystemWithRankZero.neg_mem {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) : -ψ ∈ Ψ := by
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  have h := hv.2 ψ hψ
  rwa [hv.1, two_smul, sub_add_cancel_left] at h

/-- An affine functional with zero derivative is constant. -/
theorem apply_eq_apply_of_linear_eq_zero {f : A →ᵃ[ℝ] ℝ} (hf : f.linear = 0) (x y : A) :
    f x = f y := by
  have h := f.linearMap_vsub x y
  rw [hf, LinearMap.zero_apply, vsub_eq_sub] at h
  linarith

/-- KP's literal AR 1 for a nonempty affine root system: `Ψ` spans `A*`. Two distinct roots with
the same derivative (corrected AR 4) differ by a nonzero constant, so the span of `Ψ` contains
the constants, and it maps onto `V* = span ∇Ψ`. -/
theorem IsAffineRootSystemWithRankZero.span_eq_top {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hne : Ψ.Nonempty) : Submodule.span ℝ Ψ = ⊤ := by
  obtain ⟨ψ, hψ⟩ := hne
  obtain ⟨η, ⟨hη, hηψ⟩, hηne⟩ :=
    (hΨ.infinite_fiber ψ hψ).exists_notMem_finite (Set.finite_singleton ψ)
  obtain ⟨p⟩ : Nonempty A := inferInstance
  have hc : η - ψ ∈ Submodule.span ℝ Ψ :=
    Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hψ)
  have hc_lin : (η - ψ).linear = 0 := by
    change derivativeMap (η - ψ) = 0
    rw [map_sub, sub_eq_zero]
    exact hηψ
  have hcp : (η - ψ) p ≠ 0 := by
    intro h0
    refine hηne (Set.mem_singleton_iff.2 (sub_eq_zero.1 (AffineMap.ext fun x => ?_)))
    rw [apply_eq_apply_of_linear_eq_zero hc_lin x p, h0]
    rfl
  have hconst : ∀ f : A →ᵃ[ℝ] ℝ, f.linear = 0 → f ∈ Submodule.span ℝ Ψ := by
    intro f hf
    have hfc : f = (f p / (η - ψ) p) • (η - ψ) := by
      ext x
      rw [AffineMap.coe_smul, Pi.smul_apply, apply_eq_apply_of_linear_eq_zero hf x p,
        apply_eq_apply_of_linear_eq_zero hc_lin x p, smul_eq_mul, div_mul_cancel₀ _ hcp]
    rw [hfc]
    exact Submodule.smul_mem _ _ hc
  refine eq_top_iff.2 fun f _ => ?_
  have hf : derivativeMap f ∈ (Submodule.span ℝ Ψ).map derivativeMap := by
    rw [Submodule.map_span, ← derivativeRoots_eq_image, hΨ.span_derivativeRoots_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hg, hgf⟩ := hf
  rw [← add_sub_cancel g f]
  refine Submodule.add_mem _ hg (hconst _ ?_)
  change derivativeMap (f - g) = 0
  rw [map_sub, hgf, sub_self]

/-- Rank zero: the empty set is an affine root system exactly on a point, i.e. when `V = 0`
(KP, after Definition 1.3.1: the rank `dim V` is positive precisely when `Ψ ≠ ∅`). -/
theorem isAffineRootSystemWithRankZero_empty_iff :
    IsAffineRootSystemWithRankZero (∅ : Set (A →ᵃ[ℝ] ℝ)) ↔ Subsingleton V := by
  constructor
  · intro h
    have h1 := h.span_derivativeRoots_eq_top
    rw [derivativeRoots, Set.image_empty, Submodule.span_empty] at h1
    rw [← Module.subsingleton_dual_iff ℝ]
    refine ⟨fun φ χ => ?_⟩
    have hφ : φ ∈ (⊥ : Submodule ℝ (Module.Dual ℝ V)) := h1 ▸ Submodule.mem_top
    have hχ : χ ∈ (⊥ : Submodule ℝ (Module.Dual ℝ V)) := h1 ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hφ hχ
    rw [hφ, hχ]
  · intro hV
    have hzero : ∀ φ : Module.Dual ℝ V, φ = 0 := fun φ =>
      LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply]
    refine ⟨eq_top_iff.2 fun φ _ => hzero φ ▸ Submodule.zero_mem _, by simp,
      by simp [derivativeRoots], by simp, by simp, by simp, by simp⟩

/-- An affine root system is nonempty exactly when its rank `dim V` is positive (KP, after
Definition 1.3.1). -/
theorem IsAffineRootSystemWithRankZero.nonempty_iff_nontrivial {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsAffineRootSystemWithRankZero Ψ) : Ψ.Nonempty ↔ Nontrivial V := by
  constructor
  · rintro ⟨ψ, hψ⟩
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hΨ.linear_ne_zero ψ hψ
      (LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply])
  · intro hV
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    exact not_subsingleton V (isAffineRootSystemWithRankZero_empty_iff.1 hΨ)

/-- For an affine root system the coroot vector `ψ̇∨` of AR 2 is unique (KP Remark 1.3.2(2),
via Bourbaki's uniqueness lemma, Mathlib's `Module.Dual.eq_of_preReflection_mapsTo`). -/
theorem IsAffineRootSystemWithRankZero.isCoroot_unique {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
    {ψ : A →ᵃ[ℝ] ℝ} {v w : V} (hv : IsCoroot Ψ ψ v) (hw : IsCoroot Ψ ψ w) : v = w := by
  have hmaps : ∀ u : V, IsCoroot Ψ ψ u →
      Set.MapsTo (Module.preReflection ψ.linear (Module.Dual.eval ℝ V u))
        (derivativeRoots Ψ) (derivativeRoots Ψ) := by
    rintro u hu _ ⟨η, hη, rfl⟩
    refine ⟨η - η.linear u • ψ, hu.2 η hη, ?_⟩
    simp [Module.preReflection_apply]
  have h := Module.Dual.eq_of_preReflection_mapsTo hΨ.finite_derivativeRoots
    hΨ.span_derivativeRoots_eq_top (by simpa using hv.1) (hmaps v hv)
    (by simpa using hw.1) (hmaps w hw)
  exact Module.eval_apply_injective ℝ h


end Langlands.Geometry.Building.AffineRootSystem
