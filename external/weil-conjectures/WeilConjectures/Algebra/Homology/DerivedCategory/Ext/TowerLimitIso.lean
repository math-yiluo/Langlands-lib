/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit

/-!
# `Ext` into the limit of a tower: the Milnor sequence

Let `C` be an abelian category with K-injective resolutions and exact countable products, and
`F : ℕᵒᵖ ⥤ C` a tower with limit `c` for which the Milnor sequence
`0 ⟶ lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0` is short exact (e.g. a tower of epimorphisms in a replete
topos). Its long exact `Ext`-sequence gives the Milnor exact sequence
`0 ⟶ lim¹ Ext X Fₙ (q - 1) ⟶ Ext X (lim Fₙ) q ⟶ lim Ext X Fₙ q ⟶ 0`, in the following form:

* `CategoryTheory.Abelian.Ext.exists_comp_eq_of_isLimit_tower`: every compatible family of
  classes in `Ext X Fₙ q` comes from `Ext X (lim Fₙ) q`;
* `CategoryTheory.Abelian.Ext.eq_zero_of_isLimit_tower`: a class of `Ext X (lim Fₙ) (q + 1)`
  vanishing in every `Ext X Fₙ (q + 1)` is zero, provided `lim¹ Ext X Fₙ q = 0`, i.e. `1 - t` is
  surjective on `∏ Ext X Fₙ q` (e.g. when these groups are finite,
  `AddCommGroup.exists_sub_map_succ_eq_of_finite`).

This identifies `Hⁱ(X, ℤ_ℓ)` with `lim Hⁱ(X, ℤ/ℓᵐ)` when the latter groups are finite.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite DerivedCategory

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
  {F : ℕᵒᵖ ⥤ C}

/-- The Milnor short complex `lim Fₙ ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ`. -/
private noncomputable def milnorShortComplex (c : Cone F) : ShortComplex C :=
  ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero (productIsProduct _)
    (Pi.lift fun n ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (fun n ↦ by simp) c)

omit [HasExt C] [HasDerivedCategory C] [HasKInjectiveResolutions C]
  [HasExactLimitsOfShape (Discrete ℕ) C] in
private lemma milnorShortComplex_shortExact
    (hF : ∀ ⦃P : Fan fun n : ℕ ↦ F.obj (op n)⦄ (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) →
        Epi (𝟙 P.pt - t))
    {c : Cone F} (hc : IsLimit c) : (milnorShortComplex c).ShortExact := by
  have hK := Fan.IsLimit.isLimitKernelForkOneSub (productIsProduct _)
    (Pi.lift fun n ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (fun n ↦ by simp) hc
  exact { exact := (milnorShortComplex c).exact_of_f_is_kernel hK
          mono_f := Fork.IsLimit.mono hK
          epi_g := hF (productIsProduct _) _ fun n ↦ by simp }

omit [HasExt C] [HasDerivedCategory C] [HasKInjectiveResolutions C]
  [HasExactLimitsOfShape (Discrete ℕ) C] in
private lemma milnorShortComplex_f_proj (c : Cone F) (n : ℕ) :
    (milnorShortComplex c).f ≫ Pi.π (fun n : ℕ ↦ F.obj (op n)) n = c.π.app (op n) :=
  Fan.IsLimit.fac (productIsProduct _) _ n

omit [HasExt C] [HasDerivedCategory C] [HasKInjectiveResolutions C]
  [HasExactLimitsOfShape (Discrete ℕ) C] in
private lemma milnorShortComplex_g_proj (c : Cone F) (n : ℕ) :
    (milnorShortComplex c).g ≫ Pi.π (fun n : ℕ ↦ F.obj (op n)) n =
      Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
  simp [milnorShortComplex, Preadditive.sub_comp]

omit [HasDerivedCategory C] [HasKInjectiveResolutions C]
  [HasExactLimitsOfShape (Discrete ℕ) C] in
private lemma comp_milnorShortComplex_g_comp {X : C} (c : Cone F) {q : ℕ}
    (z : Ext X (∏ᶜ fun n : ℕ ↦ F.obj (op n)) q) (n : ℕ) :
    (z.comp (mk₀ (milnorShortComplex c).g) (add_zero q)).comp
        (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) n)) (add_zero q) =
      z.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) n)) (add_zero q) -
        (z.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1))) (add_zero q)).comp
          (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero q) := by
  simp only [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, milnorShortComplex_g_proj,
    sub_eq_add_neg, mk₀_add, mk₀_neg, comp_add, comp_neg]

/-- **Surjectivity of `Ext X (lim Fₙ) q ⟶ lim Ext X Fₙ q`.** Every compatible family of classes
`zₙ ∈ Ext X Fₙ q` is the image of a class of `Ext X (lim Fₙ) q`. -/
theorem exists_comp_eq_of_isLimit_tower (X : C)
    (hF : ∀ ⦃P : Fan fun n : ℕ ↦ F.obj (op n)⦄ (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) →
        Epi (𝟙 P.pt - t))
    {c : Cone F} (hc : IsLimit c) {q : ℕ} (z : ∀ n, Ext X (F.obj (op n)) q)
    (hz : ∀ n, (z (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero q) = z n) :
    ∃ x : Ext X c.pt q, ∀ n, x.comp (mk₀ (c.π.app (op n))) (add_zero q) = z n := by
  have hS := milnorShortComplex_shortExact hF hc
  have hφ := bijective_comp_mk₀_proj X (productIsProduct fun n : ℕ ↦ F.obj (op n)) q
  obtain ⟨y, hy⟩ := hφ.2 z
  have hy' (n : ℕ) : y.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) n)) (add_zero q) = z n :=
    congrFun hy n
  have hyg : y.comp (mk₀ (milnorShortComplex c).g) (add_zero q) = 0 := by
    refine hφ.1 (funext fun n ↦ ?_)
    dsimp only
    erw [comp_milnorShortComplex_g_comp, hy', hy', hz, sub_self, zero_comp]
  obtain ⟨x, hx⟩ := covariant_sequence_exact₂ X hS y hyg
  refine ⟨x, fun n ↦ ?_⟩
  rw [← milnorShortComplex_f_proj, ← mk₀_comp_mk₀, ← comp_assoc_of_third_deg_zero, hx]
  exact hy' n

/-- **Injectivity of `Ext X (lim Fₙ) (q + 1) ⟶ lim Ext X Fₙ (q + 1)`** when `lim¹ Ext X Fₙ q`
vanishes, i.e. when `(xₙ) ↦ (xₙ - t xₙ₊₁)` is surjective on `∏ Ext X Fₙ q`. -/
theorem eq_zero_of_isLimit_tower (X : C)
    (hF : ∀ ⦃P : Fan fun n : ℕ ↦ F.obj (op n)⦄ (_ : IsLimit P) (t : P.pt ⟶ P.pt),
      (∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op) →
        Epi (𝟙 P.pt - t))
    {c : Cone F} (hc : IsLimit c) {q : ℕ}
    (hlim : ∀ y : ∀ n, Ext X (F.obj (op n)) q, ∃ x : ∀ n, Ext X (F.obj (op n)) q,
      ∀ n, x n - (x (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero q) = y n)
    (x : Ext X c.pt (q + 1))
    (hx : ∀ n, x.comp (mk₀ (c.π.app (op n))) (add_zero (q + 1)) = 0) : x = 0 := by
  have hS := milnorShortComplex_shortExact hF hc
  have hφ (m : ℕ) := bijective_comp_mk₀_proj X (productIsProduct fun n : ℕ ↦ F.obj (op n)) m
  have hx₁ : x.comp (mk₀ (milnorShortComplex c).f) (add_zero (q + 1)) = 0 := by
    refine (hφ (q + 1)).1 (funext fun n ↦ ?_)
    simp only [zero_comp]
    erw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, milnorShortComplex_f_proj]
    exact hx n
  obtain ⟨x₃, rfl⟩ := covariant_sequence_exact₁ X hS x hx₁ rfl
  -- `x₃` lies in the image of `1 - t`
  obtain ⟨w, hw⟩ := hlim fun n ↦ x₃.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) n)) (add_zero q)
  replace hw (n : ℕ) : w n - (w (n + 1)).comp (mk₀ (F.map (homOfLE n.le_succ).op)) (add_zero q) =
      x₃.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) n)) (add_zero q) := hw n
  obtain ⟨z, hz⟩ := (hφ q).2 w
  have hz' (k : ℕ) : z.comp (mk₀ (Pi.π (fun n : ℕ ↦ F.obj (op n)) k)) (add_zero q) = w k :=
    congrFun hz k
  have hx₃ : z.comp (mk₀ (milnorShortComplex c).g) (add_zero q) = x₃ := by
    refine (hφ q).1 (funext fun n ↦ ?_)
    dsimp only
    erw [comp_milnorShortComplex_g_comp, hz', hz']
    exact hw n
  rw [← hx₃, comp_assoc_of_second_deg_zero, hS.comp_extClass, comp_zero]

end CategoryTheory.Abelian.Ext
