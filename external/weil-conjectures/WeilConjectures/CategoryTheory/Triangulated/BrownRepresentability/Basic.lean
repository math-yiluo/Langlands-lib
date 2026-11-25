/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Localization
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Telescope

/-!
# Brown representability for compactly generated triangulated categories

Let `C` be a pretriangulated category with `Hom`-types in `Type v` and coproducts indexed by
types in `Type v`, and let `S : ι → C` (`ι : Type v`) be a family of *compact generators*
(`BrownRepresentability.CompactGenerators`): the family is closed under shifts up to isomorphism,
each `S i` is compact, and an object `X` with `Hom(S i, X) = 0` for all `i` is zero.

We prove **Brown representability** (Neeman; Stacks Lemma 13.38.1 for `D(R)`): every additive
cohomological functor `H : Cᵒᵖ ⥤ Ab` which sends coproducts to products is representable
(`BrownRepresentability.exists_bijective`). As a consequence, a triangulated functor out of `C`
which preserves coproducts is a left adjoint
(`Functor.isLeftAdjoint_of_compactGenerators`).

## The proof

* Given `(W, w ∈ H(W))`, we build a sequence `X₀ ⟶ X₁ ⟶ ⋯` with compatible elements
  `uₙ ∈ H(Xₙ)`: `X₀ = W ⊞ ∐_{x ∈ H(S i)} S i`, so that `Hom(S i, X₀) ⟶ H(S i)` is surjective,
  and `Xₙ₊₁` is the cone of `∐ S i ⟶ Xₙ`, the coproduct being over the morphisms
  `g : S i ⟶ Xₙ` with `H(g)(uₙ) = 0`. The telescope `X` of this sequence carries an element
  `u ∈ H(X)` for which `Hom(S i, X) ⟶ H(S i)` is bijective, by compactness of the `S i`
  (`BrownRepresentability.exists_isUniversalOn`).
* Two such universal pairs related by a morphism `g` are isomorphic via `g`, since the cone of `g`
  has no nonzero morphisms from the generators (`BrownRepresentability.isIso_of_isUniversalOn`).
* Injectivity of `Hom(Y, X) ⟶ H(Y)`: if `H(f)(u) = 0`, then `u` extends to the cone `C(f)` of
  `f`, and applying the construction to `C(f)` shows that `X ⟶ C(f)` is a split monomorphism,
  hence `f = 0`. Surjectivity: given `y ∈ H(Y)`, applying the construction to `X ⊞ Y` shows that
  `X ⟶ X ⊞ Y ⟶ X'` is an isomorphism, which gives a preimage of `y`.

This is the abstract input for Stacks Tag 0F5Y, used in the blueprint node
`theorem-existence-exceptional-inverse-image--1`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite Pretriangulated Category ZeroObject

namespace CategoryTheory.BrownRepresentability

variable {C : Type u} [Category.{v} C]

section Helpers

variable [Preadditive C] (H : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/-- `H(0) = 0` for an additive functor `H : Cᵒᵖ ⥤ Ab`. -/
@[simp]
lemma map_zero_apply [H.Additive] {A B : C} (y : H.obj (op B)) : H.map (0 : A ⟶ B).op y = 0 := by
  rw [op_zero, H.map_zero]
  rfl

omit [Preadditive C] in
/-- `H(𝟙) = 𝟙` on elements. -/
@[simp]
lemma map_id_apply {A : C} (y : H.obj (op A)) : H.map (𝟙 A).op y = y := by
  simp

omit [Preadditive C] in
/-- `H(g⁻¹)(H(g)(y)) = y` for an isomorphism `g`. -/
lemma map_inv_apply {A B : C} (g : A ⟶ B) [IsIso g] (y : H.obj (op B)) :
    H.map (inv g).op (H.map g.op y) = y := by
  rw [← map_comp_apply, IsIso.inv_hom_id, map_id_apply]

/-- The element `H(fst)(x) + H(snd)(y)` of `H(A ⊞ B)` restricts to `x` on `A`. -/
lemma map_inl_apply [H.Additive] [HasBinaryBiproducts C] {A B : C} (x : H.obj (op A))
    (y : H.obj (op B)) :
    H.map (biprod.inl : A ⟶ A ⊞ B).op (H.map biprod.fst.op x + H.map biprod.snd.op y) = x := by
  rw [map_add, ← map_comp_apply, ← map_comp_apply]
  simp

/-- The element `H(fst)(x) + H(snd)(y)` of `H(A ⊞ B)` restricts to `y` on `B`. -/
lemma map_inr_apply [H.Additive] [HasBinaryBiproducts C] {A B : C} (x : H.obj (op A))
    (y : H.obj (op B)) :
    H.map (biprod.inr : B ⟶ A ⊞ B).op (H.map biprod.fst.op x + H.map biprod.snd.op y) = y := by
  rw [map_add, ← map_comp_apply, ← map_comp_apply]
  simp

omit [Preadditive C] in
/-- If `H` sends coproducts to products, an element of `H(∐ Xⱼ)` is uniquely determined by its
restrictions to the summands, which can be prescribed arbitrarily. -/
lemma existsUnique_sigma (hH' : SendsCoproductsToProducts H) {J : Type v} (X : J → C)
    [HasCoproduct X] (x : ∀ j, H.obj (op (X j))) :
    ∃! y : H.obj (op (∐ X)), ∀ j, H.map (Sigma.ι X j).op y = x j :=
  hH' _ (coproductIsCoproduct X) x

end Helpers

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A family `S` of objects is a family of *compact generators* if it is closed under shifts up to
isomorphism, consists of compact objects, and detects zero objects. -/
structure CompactGenerators {ι : Type v} (S : ι → C) : Prop where
  exists_iso_shift (i : ι) (n : ℤ) : ∃ j, Nonempty (S j ≅ (S i)⟦n⟧)
  isCompactObj (i : ι) : IsCompactObj (S i)
  isZero_of_forall_eq_zero (X : C) (hX : ∀ i (f : S i ⟶ X), f = 0) : IsZero X

/-- A pair `(X, u ∈ H(X))` is *universal on `S`* if `Hom(S i, X) ⟶ H(S i)`, `f ↦ H(f)(u)`, is
bijective for all `i`. -/
def IsUniversalOn {ι : Type v} (S : ι → C) (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (X : C)
    (u : H.obj (op X)) : Prop :=
  ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ H.map f.op u)

variable [HasCoproducts.{v} C] {ι : Type v} {S : ι → C} (hS : CompactGenerators S)
  (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.Additive] (hH : IsCohomological H)
  (hH' : SendsCoproductsToProducts H)

omit [H.Additive] in
include hH hH' in
/-- One step of the construction: kill the morphisms `g : S i ⟶ X` with `H(g)(u) = 0` by
passing to the cone of `∐ S i ⟶ X`, to which `u` extends. -/
lemma exists_step (X : C) (u : H.obj (op X)) :
    ∃ (Y : C) (v : H.obj (op Y)) (a : X ⟶ Y), H.map a.op v = u ∧
      ∀ i (g : S i ⟶ X), H.map g.op u = 0 → g ≫ a = 0 := by
  let K := Σ i, {g : S i ⟶ X // H.map g.op u = 0}
  let κ : ∐ (fun p : K ↦ S p.1) ⟶ X := Sigma.desc fun p ↦ p.2.1
  obtain ⟨Y, a, δ, hT⟩ := distinguished_cocone_triangle κ
  have hκ : H.map κ.op u = 0 := by
    obtain ⟨y, -, hy⟩ := existsUnique_sigma H hH' (fun p : K ↦ S p.1) (fun _ ↦ 0)
    refine (hy _ fun p ↦ ?_).trans (hy 0 fun _ ↦ map_zero _).symm
    rw [← map_comp_apply]
    simpa [κ] using p.2.2
  obtain ⟨v, hv⟩ := hH _ hT u hκ
  refine ⟨Y, v, a, hv, fun i g hg ↦ ?_⟩
  have : g = Sigma.ι (fun p : K ↦ S p.1) ⟨i, g, hg⟩ ≫ κ := by simp [κ]
  have hκa : κ ≫ a = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [this, assoc, hκa, comp_zero]

include hS hH hH' in
/-- The main construction: every pair `(W, w ∈ H(W))` maps to a pair `(X, u)` which is
universal on the compact generators. -/
lemma exists_isUniversalOn (W : C) (w : H.obj (op W)) :
    ∃ (X : C) (u : H.obj (op X)) (j : W ⟶ X), H.map j.op u = w ∧ IsUniversalOn S H X u := by
  let P := Σ i, H.obj (op (S i))
  obtain ⟨y, hy, -⟩ := existsUnique_sigma H hH' (fun p : P ↦ S p.1) (fun p ↦ p.2)
  let X₀ := W ⊞ ∐ (fun p : P ↦ S p.1)
  let u₀ : H.obj (op X₀) := H.map biprod.fst.op w + H.map biprod.snd.op y
  choose next v a hv ha using exists_step (S := S) H hH hH'
  let stage : ℕ → Σ X : C, H.obj (op X) :=
    fun n ↦ Nat.rec ⟨X₀, u₀⟩ (fun _ p ↦ ⟨next p.1 p.2, v p.1 p.2⟩) n
  let Xs : ℕ → C := fun n ↦ (stage n).1
  let as : ∀ n, Xs n ⟶ Xs (n + 1) := fun n ↦ a (stage n).1 (stage n).2
  obtain ⟨Z, π, δ, hT⟩ :=
    distinguished_cocone_triangle (𝟙 (Telescope.sum Xs) - Telescope.shift Xs as)
  obtain ⟨z, hz⟩ := Telescope.exists_lift hT H hH hH' (fun n ↦ (stage n).2)
    (fun n ↦ hv _ _)
  have hz0 : H.map (Telescope.ι Xs 0 ≫ π).op z = u₀ := hz 0
  have hzN : ∀ N, H.map (Telescope.ι Xs N ≫ π).op z = (stage N).2 := hz
  refine ⟨Z, z, biprod.inl ≫ Telescope.ι Xs 0 ≫ π, ?_, fun i ↦ ⟨fun f₁ f₂ h ↦ ?_, fun x ↦ ?_⟩⟩
  · rw [map_comp_apply]
    refine (congrArg (H.map (biprod.inl : W ⟶ X₀).op) hz0).trans ?_
    exact map_inl_apply H w y
  · rw [← sub_eq_zero]
    have hf : H.map (f₁ - f₂).op z = 0 := by
      rw [map_sub_apply]
      exact sub_eq_zero.2 h
    obtain ⟨j, ⟨e⟩⟩ := hS.exists_iso_shift i (-1)
    obtain ⟨N, g, hg⟩ := Telescope.exists_factor hT (hS.isCompactObj i) (hS.isCompactObj j) e
      (f₁ - f₂)
    rw [hg, map_comp_apply, hzN N] at hf
    rw [hg, Telescope.ι_π hT, ← assoc, show g ≫ as N = 0 from ha _ _ i g hf, zero_comp]
  · refine ⟨Sigma.ι (fun p : P ↦ S p.1) ⟨i, x⟩ ≫ biprod.inr ≫ Telescope.ι Xs 0 ≫ π, ?_⟩
    dsimp only
    rw [map_comp_apply, map_comp_apply]
    refine (congrArg (fun t ↦ H.map (Sigma.ι (fun p : P ↦ S p.1) ⟨i, x⟩).op
      (H.map (biprod.inr : _ ⟶ X₀).op t)) hz0).trans ?_
    dsimp only
    rw [map_inr_apply]
    exact hy ⟨i, x⟩

omit [HasCoproducts.{v} C] [H.Additive] in
include hS in
/-- A morphism between universal pairs which is compatible with the elements is an
isomorphism. -/
lemma isIso_of_isUniversalOn {X X' : C} {u : H.obj (op X)} {u' : H.obj (op X')}
    (hu : IsUniversalOn S H X u) (hu' : IsUniversalOn S H X' u') (g : X ⟶ X')
    (hg : H.map g.op u' = u) : IsIso g := by
  have hbij : ∀ i, Function.Bijective (fun f : S i ⟶ X ↦ f ≫ g) := by
    intro i
    refine (Function.Bijective.of_comp_iff' (hu' i) _).1 ?_
    convert hu i using 1
    ext f
    simp only [Function.comp_apply, map_comp_apply, hg]
  obtain ⟨Z, p, δ, hT⟩ := distinguished_cocone_triangle g
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hS.isZero_of_forall_eq_zero _ fun i f ↦ ?_)
  obtain ⟨j, ⟨e⟩⟩ := hS.exists_iso_shift i (-1)
  have h₁ : f ≫ δ = 0 := by
    refine eq_zero_of_comp_shift_eq_zero e g (fun f' hf' ↦ (hbij j).1 ?_) _ ?_
    · simpa using hf'
    · have : δ ≫ g⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
      rw [assoc, this, comp_zero]
  obtain ⟨f', rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
  obtain ⟨f'', rfl⟩ := (hbij i).2 f'
  have : g ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
  simp [this]

include hS hH hH' in
/-- **Brown representability** (Stacks Lemma 13.38.1, the abstract input of Stacks Tag 0F5Y): if
`C` has a family of compact generators, every additive cohomological functor
`H : Cᵒᵖ ⥤ Ab` which sends coproducts to products is representable. -/
theorem exists_bijective :
    ∃ (X : C) (u : H.obj (op X)), ∀ Y, Function.Bijective (fun f : Y ⟶ X ↦ H.map f.op u) := by
  obtain ⟨X, u, -, -, hu⟩ := exists_isUniversalOn hS H hH hH' 0 0
  have hinj : ∀ {Y : C} (f : Y ⟶ X), H.map f.op u = 0 → f = 0 := by
    intro Y f hf
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle f
    obtain ⟨c, hc⟩ := hH _ hT u hf
    obtain ⟨X', u', j, hj, hu'⟩ := exists_isUniversalOn hS H hH hH' Z c
    have : IsIso (g ≫ j) := isIso_of_isUniversalOn hS H hu hu' _ (by
      rw [map_comp_apply, hj]
      exact hc)
    have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [← cancel_mono (g ≫ j), reassoc_of% hfg, zero_comp, zero_comp]
  refine ⟨X, u, fun Y ↦ ⟨fun f₁ f₂ h ↦ ?_, fun y ↦ ?_⟩⟩
  · rw [← sub_eq_zero]
    refine hinj _ ?_
    rw [map_sub_apply]
    exact sub_eq_zero.2 h
  · obtain ⟨X', u', j, hj, hu'⟩ := exists_isUniversalOn hS H hH hH' (X ⊞ Y)
      (H.map biprod.fst.op u + H.map biprod.snd.op y)
    have : IsIso (biprod.inl ≫ j) := isIso_of_isUniversalOn hS H hu hu' _ (by
      rw [map_comp_apply, hj, map_inl_apply])
    refine ⟨biprod.inr ≫ j ≫ inv (biprod.inl ≫ j), ?_⟩
    dsimp only
    have h₁ : H.map (inv (biprod.inl ≫ j)).op u = u' := by
      conv_lhs => rw [← show H.map (biprod.inl ≫ j).op u' = u by
        rw [map_comp_apply, hj, map_inl_apply]]
      exact map_inv_apply H _ _
    rw [map_comp_apply, map_comp_apply, h₁, hj, map_inr_apply]

end CategoryTheory.BrownRepresentability

namespace CategoryTheory.Functor

open BrownRepresentability

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]

/-- For a functor `F : C ⥤ D` preserving coproducts and `Y : D`, the functor
`W ↦ Hom(F(W), Y)` sends coproducts to products. -/
lemma sendsCoproductsToProducts_comp_preadditiveYoneda [Preadditive D] (F : C ⥤ D)
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] (Y : D) :
    SendsCoproductsToProducts (F.op ⋙ preadditiveYoneda.obj Y) := by
  intro J X c hc (x : ∀ j, F.obj (X j) ⟶ Y)
  let hc' := isColimitOfPreserves F hc
  refine ⟨hc'.desc (Cocone.mk Y (Discrete.natTrans fun j ↦ x j.as)), fun j ↦ ?_,
    fun y hy ↦ hc'.hom_ext fun j ↦ ?_⟩
  · exact hc'.fac _ ⟨j⟩
  · rw [hc'.fac]
    exact hy j.as

variable [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- For a triangulated functor `F : C ⥤ D` and `Y : D`, the functor `W ↦ Hom(F(W), Y)` is
cohomological. -/
lemma isCohomological_comp_preadditiveYoneda (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (Y : D) : IsCohomological (F.op ⋙ preadditiveYoneda.obj Y) := by
  intro T hT (x : F.obj T.obj₂ ⟶ Y) (hx : F.map T.mor₁ ≫ x = 0)
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ (F.map_distinguished T hT) x hx
  exact ⟨y, hy.symm⟩

/-- **Brown representability, adjoint functor form** (Stacks Tag 0F5Y, abstract form; blueprint
`theorem-existence-exceptional-inverse-image--1`): if `C` has a family of compact generators, every
triangulated functor `F : C ⥤ D` which preserves coproducts is a left adjoint. -/
theorem isLeftAdjoint_of_compactGenerators [HasCoproducts.{v} C] {ι : Type v} {S : ι → C}
    (hS : CompactGenerators S) (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] : F.IsLeftAdjoint := by
  have h (Y : D) : ∃ (X : C) (u : F.obj X ⟶ Y),
      ∀ W, Function.Bijective (fun f : W ⟶ X ↦ F.map f ≫ u) :=
    exists_bijective hS (F.op ⋙ preadditiveYoneda.obj Y)
      (isCohomological_comp_preadditiveYoneda F Y)
      (sendsCoproductsToProducts_comp_preadditiveYoneda F Y)
  choose G u hu using h
  exact isLeftAdjoint_of_bijective F u hu

end CategoryTheory.Functor
