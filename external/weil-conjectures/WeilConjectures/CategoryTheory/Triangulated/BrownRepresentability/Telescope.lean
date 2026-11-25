/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Telescopes and compact objects in a pretriangulated category

This file contains the preliminaries for Brown representability
(see `WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic`).

Let `C` be a pretriangulated category whose `Hom`-types live in `Type v` and which has
coproducts indexed by types in `Type v`.

* A functor `H : Cᵒᵖ ⥤ Ab` is *cohomological* (`BrownRepresentability.IsCohomological`) if it
  sends a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` to an exact sequence
  `H(Z) ⟶ H(Y) ⟶ H(X)`, and it *sends coproducts to products*
  (`BrownRepresentability.SendsCoproductsToProducts`) if `H(∐ Xⱼ) ⟶ ∏ H(Xⱼ)` is bijective.
* An object `s` is *compact* (`BrownRepresentability.IsCompactObj`) if every morphism from `s`
  to a coproduct `∐ Xⱼ` is a finite sum of morphisms factoring through the summands.
* Given a sequence `X₀ ⟶ X₁ ⟶ ⋯` with transition maps `aₙ`, a *telescope* (homotopy colimit)
  is a distinguished triangle `∐ Xₙ ⟶ ∐ Xₙ ⟶ Z ⟶ (∐ Xₙ)⟦1⟧` whose first map is `𝟙 - t`, where
  `t` maps the summand `Xₙ` to the summand `Xₙ₊₁` by `aₙ`. We show that a compatible family of
  elements of `H(Xₙ)` lifts to `H(Z)` (`BrownRepresentability.Telescope.exists_lift`), and that
  every morphism from a compact object `s` to `Z` factors through one of the `Xₙ`
  (`BrownRepresentability.Telescope.exists_factor`), provided `s⟦-1⟧` is (isomorphic to) a
  compact object.

These are the ingredients of the proof of Brown representability, Stacks Tag 0F5Y (via Stacks
Lemma 13.38.1 for the derived category of a ring), used in the blueprint node
`theorem-existence-exceptional-inverse-image--1`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated Category

namespace CategoryTheory.BrownRepresentability

variable {C : Type u} [Category.{v} C]

section Defs

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A functor `H : Cᵒᵖ ⥤ Ab` is *cohomological* if for every distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` the sequence `H(Z) ⟶ H(Y) ⟶ H(X)` is exact. -/
def IsCohomological (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ T ∈ distTriang C, ∀ x : H.obj (op T.obj₂), H.map T.mor₁.op x = 0 →
    ∃ y : H.obj (op T.obj₃), H.map T.mor₂.op y = x

end Defs

/-- `H(f ≫ g)(y) = H(f)(H(g)(y))` for a functor `H : Cᵒᵖ ⥤ Ab`. -/
lemma map_comp_apply (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (y : H.obj (op D)) : H.map (f ≫ g).op y = H.map f.op (H.map g.op y) := by
  simp

/-- `H(f - g)(y) = H(f)(y) - H(g)(y)` for an additive functor `H : Cᵒᵖ ⥤ Ab`. -/
lemma map_sub_apply [Preadditive C] (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] {A B : C}
    (f g : A ⟶ B) (y : H.obj (op B)) : H.map (f - g).op y = H.map f.op y - H.map g.op y := by
  rw [op_sub, H.map_sub]
  rfl

/-- A functor `H : Cᵒᵖ ⥤ Ab` *sends coproducts to products* if for every coproduct `∐ Xⱼ`
indexed by a type in `Type v`, the map `H(∐ Xⱼ) ⟶ ∏ H(Xⱼ)` is bijective. -/
def SendsCoproductsToProducts (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ ⦃J : Type v⦄ ⦃X : J → C⦄ (c : Cofan X), IsColimit c → ∀ x : ∀ j, H.obj (op (X j)),
    ∃! y : H.obj (op c.pt), ∀ j, H.map (c.inj j).op y = x j

/-- An object `s` of a preadditive category is *compact* if every morphism from `s` to a
coproduct `∐ Xⱼ` (indexed by a type in `Type v`) is a finite sum of morphisms factoring through
the summands. -/
def IsCompactObj [Preadditive C] (s : C) : Prop :=
  ∀ ⦃J : Type v⦄ ⦃X : J → C⦄ (c : Cofan X), IsColimit c → ∀ f : s ⟶ c.pt,
    ∃ (S : Finset J) (g : ∀ j, s ⟶ X j), f = ∑ j ∈ S, g j ≫ c.inj j

/-- Compactness is invariant under isomorphism. -/
lemma IsCompactObj.of_iso [Preadditive C] {s s' : C} (hs : IsCompactObj s) (e : s' ≅ s) :
    IsCompactObj s' := by
  intro J X c hc f
  obtain ⟨S, g, hg⟩ := hs c hc (e.inv ≫ f)
  refine ⟨S, fun j ↦ e.hom ≫ g j, ?_⟩
  simp only [assoc, ← Preadditive.comp_sum, ← hg, Iso.hom_inv_id_assoc]

section Shift


variable [Preadditive C] [HasShift C ℤ]

/-- Let `s'` be isomorphic to `s⟦-1⟧`. If composition with `g : Y ⟶ Y'` is injective on
morphisms out of `s'`, then composition with `g⟦1⟧'` is injective on morphisms `s ⟶ Y⟦1⟧`. -/
lemma eq_zero_of_comp_shift_eq_zero {s s' : C} (e : s' ≅ s⟦(-1 : ℤ)⟧) {Y Y' : C} (g : Y ⟶ Y')
    (hg : ∀ f : s' ⟶ Y, f ≫ g = 0 → f = 0) (f : s ⟶ Y⟦(1 : ℤ)⟧) (hf : f ≫ g⟦(1 : ℤ)⟧' = 0) :
    f = 0 := by
  let adj := (shiftEquiv' C (-1 : ℤ) 1 (by norm_num)).toAdjunction
  have h₁ : (adj.homEquiv _ _).symm f ≫ g = 0 := by
    rw [← Adjunction.homEquiv_naturality_right_symm]
    change (adj.homEquiv _ _).symm (f ≫ g⟦(1 : ℤ)⟧') = 0
    rw [hf, Adjunction.homEquiv_counit]
    simp [adj]
  have h₂ : e.hom ≫ (adj.homEquiv _ _).symm f = 0 := hg _ (by rw [assoc, h₁, comp_zero])
  have h₃ : (adj.homEquiv _ _).symm f = 0 := by
    rw [← cancel_epi e.hom, h₂, comp_zero]
  rw [← (adj.homEquiv _ _).apply_symm_apply f, h₃, Adjunction.homEquiv_unit]
  simp [adj]

/-- Compact objects are stable under shifts. -/
lemma IsCompactObj.shift [∀ n : ℤ, (shiftFunctor C n).Additive] {s : C} (hs : IsCompactObj s)
    (n : ℤ) : IsCompactObj (s⟦n⟧) := by
  intro J X c hc f
  let adj : shiftFunctor C n ⊣ shiftFunctor C (-n) := (shiftEquiv' C n (-n) (by simp)).toAdjunction
  have hc₁ : IsColimit (Cofan.mk c.pt c.inj) := hc.ofIsoColimit (Cofan.ext (Iso.refl _) (by simp))
  have hc₂ := isColimitCofanMkObjOfIsColimit (shiftFunctor C (-n)) X c.inj hc₁
  obtain ⟨S, g, hg⟩ := hs _ hc₂ (adj.homEquiv _ _ f)
  refine ⟨S, fun j ↦ (adj.homEquiv _ _).symm (g j), ?_⟩
  rw [← (adj.homEquiv _ _).symm_apply_apply f, hg]
  simp [Adjunction.homEquiv_counit, Functor.map_sum, Preadditive.sum_comp]

end Shift

namespace Telescope

variable [HasCoproducts.{v} C] (X : ℕ → C) (a : ∀ n, X n ⟶ X (n + 1))

/-- The coproduct `∐ₙ Xₙ` of a sequence of objects, indexed by `ULift ℕ` so that it is
a coproduct indexed by a type in `Type v`. -/
noncomputable abbrev sum : C := ∐ fun k : ULift.{v} ℕ ↦ X k.down

/-- The inclusion of the `n`-th summand into `∐ₙ Xₙ`. -/
noncomputable def ι (n : ℕ) : X n ⟶ sum X := Sigma.ι (fun k : ULift.{v} ℕ ↦ X k.down) ⟨n⟩

/-- The coprojections of `∐ₙ Xₙ` are the morphisms `ι X n`. -/
@[simp]
lemma sigma_ι (k : ULift.{v} ℕ) : Sigma.ι (fun k : ULift.{v} ℕ ↦ X k.down) k = ι X k.down := rfl

/-- The coprojections of the standard cofan on `∐ₙ Xₙ` are the morphisms `ι X n`. -/
@[simp]
lemma cofan_inj (k : ULift.{v} ℕ) :
    (Cofan.mk (sum X) (Sigma.ι (fun k : ULift.{v} ℕ ↦ X k.down))).inj k = ι X k.down := rfl

/-- Composition of `ι X n` with a morphism out of the coproduct. -/
@[reassoc (attr := simp)]
lemma ι_desc {Y : C} (f : ∀ k : ULift.{v} ℕ, X k.down ⟶ Y) (n : ℕ) :
    ι X n ≫ Sigma.desc f = f ⟨n⟩ :=
  Sigma.ι_comp_desc f ⟨n⟩

/-- Morphisms out of `∐ₙ Xₙ` are determined by their restrictions to the summands. -/
@[ext]
lemma hom_ext {Y : C} {f g : sum X ⟶ Y} (h : ∀ n, ι X n ≫ f = ι X n ≫ g) : f = g :=
  Sigma.hom_ext _ _ fun k ↦ h k.down

/-- The shift endomorphism `t` of `∐ₙ Xₙ`, mapping the summand `Xₙ` to `Xₙ₊₁` by `aₙ`. -/
noncomputable def shift : sum X ⟶ sum X :=
  Sigma.desc fun k ↦ a k.down ≫ ι X (k.down + 1)

/-- The shift `t` maps the summand `Xₙ` to `Xₙ₊₁` by `aₙ`. -/
@[reassoc (attr := simp)]
lemma ι_shift (n : ℕ) : ι X n ≫ shift X a = a n ≫ ι X (n + 1) := by
  simp [shift]

open scoped Classical in
/-- The projection `∐ₙ Xₙ ⟶ Xₘ`, which is the identity on the `m`-th summand and zero on the
other summands. -/
noncomputable def proj [Preadditive C] (m : ℕ) : sum X ⟶ X m :=
  Sigma.desc (Pi.single (M := fun k : ULift.{v} ℕ ↦ X k.down ⟶ X m) ⟨m⟩ (𝟙 (X m)))

/-- The projection `∐ₙ Xₙ ⟶ Xₘ` is the identity on the summand `Xₘ`. -/
@[reassoc (attr := simp)]
lemma ι_proj_self [Preadditive C] (n : ℕ) : ι X n ≫ proj X n = 𝟙 _ := by
  simp [proj]

/-- The projection `∐ₙ Xₙ ⟶ Xₘ` vanishes on the summands `Xₙ`, `n ≠ m`. -/
@[reassoc]
lemma ι_proj_of_ne [Preadditive C] {n m : ℕ} (h : n ≠ m) : ι X n ≫ proj X m = 0 := by
  classical
  simp only [proj, ι_desc]
  convert Pi.single_eq_of_ne (fun h' ↦ h (congrArg ULift.down h')) _

/-- The image of the shift `t` does not meet the summand `X₀`. -/
lemma shift_proj_zero [Preadditive C] : shift X a ≫ proj X 0 = 0 := by
  refine hom_ext X fun n ↦ ?_
  simp [ι_proj_of_ne X (Nat.succ_ne_zero n)]

/-- The `(m + 1)`-st component of the shift `t` is `aₘ` applied to the `m`-th one. -/
lemma shift_proj_succ [Preadditive C] (m : ℕ) : shift X a ≫ proj X (m + 1) = proj X m ≫ a m := by
  refine hom_ext X fun k ↦ ?_
  by_cases h : k = m
  · subst h
    simp
  · rw [ι_shift_assoc, ι_proj_of_ne X (by lia), ι_proj_of_ne_assoc X h]
    simp

variable [Preadditive C]

/-- If `s` is compact, then composition with `𝟙 - t` is injective on morphisms `s ⟶ ∐ₙ Xₙ`. -/
lemma eq_zero_of_comp_eq_zero {s : C} (hs : IsCompactObj s) (g : s ⟶ sum X)
    (hg : g ≫ (𝟙 _ - shift X a) = 0) : g = 0 := by
  have hg' : g = g ≫ shift X a := by
    rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at hg
    exact hg
  have hp : ∀ m, g ≫ proj X m = 0 := by
    intro m
    induction m with
    | zero => rw [hg', assoc, shift_proj_zero, comp_zero]
    | succ m ih => rw [hg', assoc, shift_proj_succ, reassoc_of% ih, zero_comp]
  obtain ⟨S, f, hf⟩ := hs _ (coproductIsCoproduct _) g
  have hf' : ∀ k ∈ S, f k = 0 := by
    intro k hk
    have := hp k.down
    rw [hf, Preadditive.sum_comp, Finset.sum_eq_single k] at this
    · simpa using this
    · intro b _ hb
      rw [cofan_inj, assoc, ι_proj_of_ne X (fun h ↦ hb (ULift.ext h)), comp_zero]
    · exact fun h ↦ (h hk).elim
  rw [hf]
  exact Finset.sum_eq_zero fun k hk ↦ by rw [hf' k hk, zero_comp]

section

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] {X a} {Z : C} {π : sum X ⟶ Z} {δ : Z ⟶ (sum X)⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (𝟙 _ - shift X a) π δ ∈ distTriang C)
include hT

/-- In the telescope `Z`, the map `Xₙ ⟶ Z` factors through `aₙ : Xₙ ⟶ Xₙ₊₁`. -/
@[reassoc]
lemma ι_π (n : ℕ) : ι X n ≫ π = a n ≫ ι X (n + 1) ≫ π := by
  have : (𝟙 _ - shift X a) ≫ π = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [Preadditive.sub_comp, id_comp, sub_eq_zero] at this
  conv_lhs => rw [this]
  rw [ι_shift_assoc]

/-- A morphism to `Z` factoring through `Xₙ` factors through `Xₙ₊ₖ`. -/
lemma exists_factor_add (n k : ℕ) {s : C} (h : s ⟶ X n) :
    ∃ h' : s ⟶ X (n + k), h ≫ ι X n ≫ π = h' ≫ ι X (n + k) ≫ π := by
  induction k with
  | zero => exact ⟨h, rfl⟩
  | succ k ih =>
    obtain ⟨h', hh'⟩ := ih
    exact ⟨h' ≫ a (n + k), by rw [hh', ι_π hT, assoc]; rfl⟩

/-- A morphism to `Z` factoring through `Xₙ` factors through `X_N` for `n ≤ N`. -/
lemma exists_factor_of_le {n N : ℕ} (hnN : n ≤ N) {s : C} (h : s ⟶ X n) :
    ∃ h' : s ⟶ X N, h ≫ ι X n ≫ π = h' ≫ ι X N ≫ π := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnN
  exact exists_factor_add hT n k h

/-- A finite sum of morphisms factoring through some of the `Xₙ` factors through a single `X_N`. -/
lemma exists_factor_sum {s : C} (S : Finset (ULift.{v} ℕ)) (g : ∀ k : ULift.{v} ℕ, s ⟶ X k.down) :
    ∃ (N : ℕ) (h : s ⟶ X N), (∑ k ∈ S, g k ≫ ι X k.down) ≫ π = h ≫ ι X N ≫ π := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | insert k S hk ih =>
    obtain ⟨N, h, hh⟩ := ih
    obtain ⟨h₁, hh₁⟩ := exists_factor_of_le hT (le_max_left N k.down) h
    obtain ⟨h₂, hh₂⟩ := exists_factor_of_le hT (le_max_right N k.down) (g k)
    refine ⟨max N k.down, h₁ + h₂, ?_⟩
    rw [Finset.sum_insert hk, Preadditive.add_comp, hh, hh₁, Preadditive.add_comp, assoc, hh₂]
    abel

/-- If `s` is compact and `s⟦-1⟧` is isomorphic to a compact object, every morphism `s ⟶ Z` to
the telescope `Z` factors through one of the `Xₙ`. -/
lemma exists_factor {s s' : C} (hs : IsCompactObj s) (hs' : IsCompactObj s')
    (e : s' ≅ s⟦(-1 : ℤ)⟧) (f : s ⟶ Z) :
    ∃ (N : ℕ) (h : s ⟶ X N), f = h ≫ ι X N ≫ π := by
  have h₁ : f ≫ δ = 0 := by
    refine eq_zero_of_comp_shift_eq_zero e (𝟙 _ - shift X a)
      (fun g hg ↦ eq_zero_of_comp_eq_zero X a hs' g hg) _ ?_
    have : δ ≫ (𝟙 _ - shift X a)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
    rw [assoc, this, comp_zero]
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
  obtain ⟨S, g', hg'⟩ := hs _ (coproductIsCoproduct _) g
  obtain ⟨N, h, hh⟩ := exists_factor_sum hT S g'
  exact ⟨N, h, by rw [← hh, hg']; rfl⟩

end

omit [Preadditive C] in
/-- If `H` sends coproducts to products, an element of `H(∐ₙ Xₙ)` is uniquely determined by its
restrictions to the summands, which can be prescribed arbitrarily. -/
lemma existsUnique_sum (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (hH' : SendsCoproductsToProducts H)
    (u : ∀ n, H.obj (op (X n))) :
    ∃! x : H.obj (op (sum X)), ∀ n, H.map (ι X n).op x = u n := by
  obtain ⟨x, hx, hx'⟩ := hH' _ (coproductIsCoproduct (fun k : ULift.{v} ℕ ↦ X k.down))
    (fun k ↦ u k.down)
  exact ⟨x, fun n ↦ hx ⟨n⟩, fun y hy ↦ hx' y fun k ↦ hy k.down⟩

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] {X a} {Z : C} {π : sum X ⟶ Z} {δ : Z ⟶ (sum X)⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (𝟙 _ - shift X a) π δ ∈ distTriang C)

include hT in
/-- Let `H` be a cohomological functor which is additive and sends coproducts to products.
A compatible family of elements `uₙ ∈ H(Xₙ)` lifts to an element of `H(Z)`, where `Z` is the
telescope of the sequence. -/
lemma exists_lift (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] (hH : IsCohomological H)
    (hH' : SendsCoproductsToProducts H) (u : ∀ n, H.obj (op (X n)))
    (hu : ∀ n, H.map (a n).op (u (n + 1)) = u n) :
    ∃ v : H.obj (op Z), ∀ n, H.map (ι X n ≫ π).op v = u n := by
  obtain ⟨x, hx, -⟩ := existsUnique_sum X H hH' u
  have hx' : H.map (𝟙 _ - shift X a).op x = 0 := by
    obtain ⟨y, -, hy⟩ := existsUnique_sum X H hH' (fun _ ↦ 0)
    have e₁ := hy 0 (fun _ ↦ by simp)
    refine (hy _ fun k ↦ ?_).trans e₁.symm
    rw [← map_comp_apply, Preadditive.comp_sub, comp_id, ι_shift, map_sub_apply,
      map_comp_apply, hx k, hx (k + 1), hu]
    exact sub_self _
  obtain ⟨v, hv⟩ := hH _ hT x hx'
  replace hv : H.map π.op v = x := hv
  refine ⟨v, fun n ↦ ?_⟩
  rw [map_comp_apply]
  rw [hv]
  exact hx n

end Telescope

end CategoryTheory.BrownRepresentability
