import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConjugationBound

/-! # Lemma II.3.5: elements of small height lie in `a⁻¹ Γ a M Γ̄`

Waldspurger 2003, Lemma II.3.5: for a maximal standard parabolic subgroup `P = M U`, the
simple root `α` with `Δ₀^M = Δ₀ - {α}` and compact open subgroups `Γ ⊆ U`, `Γ̄ ⊆ Ū`, there is
`C > 0` such that `1 + σ(g) + σ(a g a⁻¹) ≤ C ⟨α, H₀(a)⟩` with `a ∈ Ā⁺₀` implies
`g ∈ a⁻¹ Γ a M Γ̄`. The proof has three steps: (2) for `g ∈ K ∩ Ū P`, through the
coordinates of `τ_P(g) e₁`; (3) for all `g`, through the Iwasawa decomposition, Lemma II.3.3
and the density of `Ū P`; and the combination of (3) for `P` and for `P̄`. This module proves
the three steps for abstract data, with the properties of `τ_P` and of the groups as
hypotheses, and deduces inequality (2) of the proof of Proposition VIII.3.1
(`ConjugationSigmaBound`).
-/

noncomputable section

open scoped Pointwise Topology
open Filter

namespace Langlands.HarishChandraSchwartz

/-- The conclusion of Lemma II.3.5: `1 + σ(g) + σ(a g a⁻¹) ≤ C t(a)` with `a ∈ A` implies
`g ∈ Ω(a)`. For Waldspurger's data `A = Ā⁺₀`, `t(a) = ⟨α, H₀(a)⟩` and
`Ω(a) = a⁻¹ Γ a M Γ̄`. -/
def OpenCellBound {G : Type*} [Group G] (σ t : G → ℝ) (A : Set G) (Ω : G → Set G) (C : ℝ) :
    Prop :=
  ∀ a ∈ A, ∀ g, 1 + σ g + σ (a * g * a⁻¹) ≤ C * t a → g ∈ Ω a

section Coordinates

variable {G ι : Type*} [Group G]

/-- Step (2) of the proof of Lemma II.3.5, from the coordinates `w(g)_i = |x_i(g)|` of
`τ_P(g) e₁ = Σ x_i(g) e_i`. Hypotheses: `|x_i(g)| ≤ exp(C₂ (1 + σ(g)))` (from
`log ‖τ_P(g) e₁‖ ≤ C₂ (1 + σ(g))`); for `k ∈ K` some `|x_i(k)| ≥ exp(-C₃)`; for `a ∈ A` and
`i ≠ i₁`, `|x_i(a g a⁻¹)| ≥ exp(C₄ t(a)) |x_i(g)|` (the characters `χ_i`); for `ū ∈ Ū` and
`p ∈ P`, `|x_i(ū p)| = c |x_i(ū)|` with `c > 0` independent of `i` (`τ_P(p) e₁ ∈ F^× e₁`);
`|x_{i₁}(ū)| = 1`; and `|x_i(ū)| ≤ exp(-C₅)` for all `i ≠ i₁` implies `ū ∈ Γ̄`. Then there is
`C₁ > 0` such that `ū p ∈ K` and `1 + σ(a ū p a⁻¹) ≤ C₁ t(a)` imply `ū ∈ Γ̄`. -/
theorem mem_of_coordinate_bounds {i₁ : ι} {w : G → ι → ℝ} {σ t : G → ℝ}
    {A K Ubar P Γbar : Set G} {C₂ C₃ C₄ C₅ : ℝ}
    (hC₂ : 0 < C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 < C₄) (hC₅ : 0 < C₅) (hσ : ∀ g, 0 ≤ σ g)
    (h1 : ∀ g i, w g i ≤ Real.exp (C₂ * (1 + σ g)))
    (h2 : ∀ k ∈ K, ∃ i, Real.exp (-C₃) ≤ w k i)
    (h3 : ∀ a ∈ A, ∀ g, ∀ i, i ≠ i₁ → Real.exp (C₄ * t a) * w g i ≤ w (a * g * a⁻¹) i)
    (h4 : ∀ u ∈ Ubar, ∀ p ∈ P, ∃ c > 0, ∀ i, w (u * p) i = c * w u i)
    (h5 : ∀ u ∈ Ubar, w u i₁ = 1)
    (h6 : ∀ u ∈ Ubar, (∀ i, i ≠ i₁ → w u i ≤ Real.exp (-C₅)) → u ∈ Γbar) :
    ∃ C₁ > 0, ∀ a ∈ A, ∀ u ∈ Ubar, ∀ p ∈ P, u * p ∈ K →
      1 + σ (a * (u * p) * a⁻¹) ≤ C₁ * t a → u ∈ Γbar := by
  set D := C₂ + C₃ + C₅
  have hD : 0 < D := by positivity
  refine ⟨C₄ / D, div_pos hC₄ hD, fun a ha u hu p hp hK hineq => ?_⟩
  set g := u * p
  set s := C₄ / D * t a
  have hs : 1 ≤ s := by linarith [hσ (a * g * a⁻¹)]
  have hDs : C₄ * t a = D * s := by
    simp only [s]
    field_simp
  have hsmall : ∀ i, i ≠ i₁ → w g i ≤ Real.exp (-C₃ - C₅) := by
    intro i hi
    have e1 := h3 a ha g i hi
    have e2 := h1 (a * g * a⁻¹) i
    have e3 : Real.exp (C₂ * (1 + σ (a * g * a⁻¹))) ≤ Real.exp (C₂ * s) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hineq hC₂.le)
    have e4 : w g i ≤ Real.exp (C₂ * s - C₄ * t a) := by
      rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos _), mul_comm]
      exact e1.trans (e2.trans e3)
    refine e4.trans (Real.exp_le_exp.mpr ?_)
    rw [hDs]
    have h35 : 0 < C₃ + C₅ := by linarith
    have : C₂ * s - D * s = -((C₃ + C₅) * s) := by simp only [D]; ring
    rw [this]
    nlinarith
  obtain ⟨i, hi⟩ := h2 g hK
  have hi₁ : i = i₁ := by
    by_contra hne
    have h' := Real.exp_le_exp.mp (hi.trans (hsmall i hne))
    linarith
  rw [hi₁] at hi
  obtain ⟨c, hc, hcw⟩ := h4 u hu p hp
  have hc₁ : Real.exp (-C₃) ≤ c := by
    have := hcw i₁
    rw [h5 u hu, mul_one] at this
    rw [← this]
    exact hi
  refine h6 u hu fun j hj => ?_
  have hj' := hsmall j hj
  rw [hcw j] at hj'
  have : c * w u j ≤ c * Real.exp (-C₅) := by
    refine hj'.trans ?_
    rw [sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hc₁ (Real.exp_pos _).le
  exact le_of_mul_le_mul_left this hc

end Coordinates

section Density

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Step (3) of the proof of Lemma II.3.5: from step (2), the Iwasawa decomposition
`G = K P₀` with `P₀ ≤ P`, Lemma II.3.3 in the form `1 + σ(a p a⁻¹) ≤ C₇ (1 + σ(p))` for
`p ∈ P₀`, the density of `Ū P`, the closedness of `Γ̄ P` and the local constancy of `σ` near
each `g` (for Waldspurger's `σ`, its bi-invariance under the open subgroup `K`):
`1 + σ(g) + σ(a g a⁻¹) ≤ (C₁ / C₇) t(a)` implies `g ∈ Γ̄ P`. -/
theorem mem_mul_of_dense {σ t : G → ℝ} {A Γbar : Set G} {K P₀ P Ubar : Subgroup G}
    (hσ : ∀ g, 0 ≤ σ g) (hsub : ∀ x y, σ (x * y) ≤ σ x + σ y) (hinv : ∀ x, σ x⁻¹ = σ x)
    (hσK : ∀ k ∈ K, ∀ g, σ (k * g) = σ g) (hP₀ : P₀ ≤ P)
    (hiwa : ∀ g, ∃ k ∈ K, ∃ p ∈ P₀, g = k * p)
    {C₇ : ℝ} (hC₇ : 1 ≤ C₇) (h33 : ∀ a ∈ A, ∀ p ∈ P₀, 1 + σ (a * p * a⁻¹) ≤ C₇ * (1 + σ p))
    {C₁ : ℝ}
    (h2 : ∀ a ∈ A, ∀ u ∈ Ubar, ∀ p ∈ P, u * p ∈ K →
      1 + σ (a * (u * p) * a⁻¹) ≤ C₁ * t a → u ∈ Γbar)
    (hdense : Dense ((Ubar : Set G) * (P : Set G))) (hclosed : IsClosed (Γbar * (P : Set G)))
    (hloc : ∀ a ∈ A, ∀ g, ∀ᶠ g' in 𝓝 g, σ g' = σ g ∧ σ (a * g' * a⁻¹) = σ (a * g * a⁻¹))
    {a : G} (ha : a ∈ A) {g : G} (hg : 1 + σ g + σ (a * g * a⁻¹) ≤ C₁ / C₇ * t a) :
    g ∈ Γbar * (P : Set G) := by
  have hC₇0 : 0 < C₇ := by linarith
  -- the case `g ∈ Ū P`
  have hcell : ∀ g', g' ∈ (Ubar : Set G) * (P : Set G) →
      1 + σ g' + σ (a * g' * a⁻¹) ≤ C₁ / C₇ * t a → g' ∈ Γbar * (P : Set G) := by
    intro g' hg' hineq
    obtain ⟨u, hu, p', hp', rfl⟩ := Set.mem_mul.mp hg'
    obtain ⟨k, hk, p, hp, hkp⟩ := hiwa (u * p')
    have hkq : k = u * (p' * p⁻¹) := by
      rw [eq_mul_inv_iff_mul_eq.mpr hkp.symm]
      group
    have hσp : σ p = σ (u * p') := by
      rw [hkp, hσK k hk]
    have hconj : a * k * a⁻¹ = (a * (u * p') * a⁻¹) * (a * p * a⁻¹)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq.mpr hkp.symm]
      group
    have hk' : 1 + σ (a * k * a⁻¹) ≤ C₁ * t a := by
      have e1 : σ (a * k * a⁻¹) ≤ σ (a * (u * p') * a⁻¹) + σ (a * p * a⁻¹) := by
        rw [hconj, ← hinv (a * p * a⁻¹)]
        exact hsub _ _
      have e2 := h33 a ha p hp
      rw [hσp] at e2
      have e3 : σ (a * (u * p') * a⁻¹) ≤ C₇ * σ (a * (u * p') * a⁻¹) :=
        le_mul_of_one_le_left (hσ _) hC₇
      have e4 : C₇ * (1 + σ (u * p') + σ (a * (u * p') * a⁻¹)) ≤ C₁ * t a := by
        calc C₇ * (1 + σ (u * p') + σ (a * (u * p') * a⁻¹))
            ≤ C₇ * (C₁ / C₇ * t a) := mul_le_mul_of_nonneg_left hineq hC₇0.le
          _ = C₁ * t a := by field_simp
      nlinarith
    have hu' : u ∈ Γbar := h2 a ha u hu (p' * p⁻¹) (P.mul_mem hp' (P.inv_mem (hP₀ hp)))
      (hkq ▸ hk) (hkq ▸ hk')
    exact Set.mul_mem_mul hu' hp'
  rw [← hclosed.closure_eq, mem_closure_iff_nhds]
  intro V hV
  obtain ⟨g', hg'cell, hg'V, hg'σ⟩ :
      ∃ g', g' ∈ (Ubar : Set G) * (P : Set G) ∧ g' ∈ V ∧
        (σ g' = σ g ∧ σ (a * g' * a⁻¹) = σ (a * g * a⁻¹)) := by
    obtain ⟨g', hg'1, hg'2, hg'3⟩ := hdense.inter_nhds_nonempty (Filter.inter_mem hV (hloc a ha g))
    exact ⟨g', hg'1, hg'2, hg'3⟩
  refine ⟨g', hg'V, hcell g' hg'cell ?_⟩
  rw [hg'σ.1, hg'σ.2]
  exact hg

end Density

section Combination

variable {G : Type*} [Group G]

/-- Lemma II.3.5 from step (3) for `P` (with `Γ̄`) and for `P̄` (with `Γ`, `a⁻¹`): if
`1 + σ(g) + σ(a g a⁻¹) ≤ C₆ t(a)` implies `g ∈ Γ̄ P`, `1 + σ(g) + σ(a⁻¹ g a) ≤ C₈ t(a)` implies
`g ∈ Γ P̄`, and `a g a⁻¹ ∈ Γ P̄`, `g⁻¹ ∈ Γ̄ P` imply `g ∈ Ω(a)` (for Waldspurger:
`a⁻¹ Γ a P̄ ∩ P Γ̄ = a⁻¹ Γ a M Γ̄`), then `OpenCellBound σ t A Ω (min C₆ C₈)`. -/
theorem openCellBound_of_mul {σ t : G → ℝ} {A : Set G} {Ω : G → Set G}
    {Γ Γbar P Pbar : Set G} (hσ : ∀ g, 0 ≤ σ g) (hinv : ∀ x, σ x⁻¹ = σ x)
    {C₆ C₈ : ℝ} (hC₆ : 0 < C₆) (hC₈ : 0 < C₈)
    (h3 : ∀ a ∈ A, ∀ g, 1 + σ g + σ (a * g * a⁻¹) ≤ C₆ * t a → g ∈ Γbar * P)
    (h3' : ∀ a ∈ A, ∀ g, 1 + σ g + σ (a⁻¹ * g * a) ≤ C₈ * t a → g ∈ Γ * Pbar)
    (hint : ∀ a ∈ A, ∀ g, a * g * a⁻¹ ∈ Γ * Pbar → g⁻¹ ∈ Γbar * P → g ∈ Ω a) :
    OpenCellBound σ t A Ω (min C₆ C₈) := by
  intro a ha g hg
  have hX : 1 ≤ 1 + σ g + σ (a * g * a⁻¹) := by linarith [hσ g, hσ (a * g * a⁻¹)]
  have ht : 0 < t a := by
    by_contra h
    rw [not_lt] at h
    have : min C₆ C₈ * t a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_min hC₆.le hC₈.le) h
    linarith
  refine hint a ha g ?_ ?_
  · refine h3' a ha _ ?_
    have : a⁻¹ * (a * g * a⁻¹) * a = g := by group
    rw [this]
    calc 1 + σ (a * g * a⁻¹) + σ g = 1 + σ g + σ (a * g * a⁻¹) := by ring
      _ ≤ min C₆ C₈ * t a := hg
      _ ≤ C₈ * t a := mul_le_mul_of_nonneg_right (min_le_right _ _) ht.le
  · refine h3 a ha _ ?_
    have : a * g⁻¹ * a⁻¹ = (a * g * a⁻¹)⁻¹ := by group
    rw [this, hinv, hinv]
    exact hg.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ht.le)

/-- Inequality (2) of the proof of Proposition VIII.3.1 from Lemma II.3.5 and inequality (1)
of that proof, `1 + σ(a) ≤ C₁ (1 + t(a))` on `T ⊆ A`: for `g` outside `Ω(a)`,
`1 + σ(a) ≤ C₂ (1 + σ(g) + σ(a g a⁻¹))`. This is `ConjugationSigmaBound σ T (Ω ·)ᶜ`, the
hypothesis of `lintegral_conj_mul_le`. -/
theorem conjugationSigmaBound_of_openCellBound {σ t : G → ℝ} {A T : Set G} {Ω : G → Set G}
    {C : ℝ} (hC : 0 < C) (hσ : ∀ g, 0 ≤ σ g) (hTA : T ⊆ A) (h : OpenCellBound σ t A Ω C)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁) (h1 : ∀ a ∈ T, 1 + σ a ≤ C₁ * (1 + t a)) :
    ConjugationSigmaBound σ T fun a => (Ω a)ᶜ := by
  refine ⟨C₁ * (1 + 1 / C), fun a ha g hg => ?_⟩
  set X := 1 + σ g + σ (a * g * a⁻¹)
  have hX : 1 ≤ X := by simp only [X]; linarith [hσ g, hσ (a * g * a⁻¹)]
  have hlt : C * t a < X := by
    by_contra hle
    rw [not_lt] at hle
    exact hg (h a (hTA ha) g hle)
  have ht : t a ≤ X / C := by
    rw [le_div_iff₀ hC]
    linarith
  calc 1 + σ a ≤ C₁ * (1 + t a) := h1 a ha
    _ ≤ C₁ * (X + X / C) := by
        apply mul_le_mul_of_nonneg_left _ hC₁
        linarith
    _ = C₁ * (1 + 1 / C) * X := by ring

end Combination

end Langlands.HarishChandraSchwartz
