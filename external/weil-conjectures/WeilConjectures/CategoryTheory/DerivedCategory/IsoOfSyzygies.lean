/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Natural transformations into a derived category which are isomorphisms by a way-out argument

Let `τ : F₁ ⟶ F₂` be a natural transformation, compatible with the shifts, between triangulated
functors from a pretriangulated category `C` to a derived category `D(A)`. Let `S` be a property
of objects of `C` such that

* the objects `F₁ X` and `F₂ X` for `X` in `S` have no homology above a common degree `B`;
* every `X` in `S` is the third object of a distinguished triangle `X₁ ⟶ P ⟶ X ⟶ X₁[1]` with `X₁`
  in `S` and `τ` an isomorphism at `P`.

Then `τ` is an isomorphism at every object of `S`
(`DerivedCategory.isIso_app_of_exists_distTriang`). This is the "way-out" argument: for a
finitely generated module `M` over a Noetherian ring, take `P` free of finite rank and `X₁` the
first syzygy of `M`. The homology of `τ` at `X` in degree `n` is compared, by the five lemma on the
long exact homology sequences, with the homology of `τ` at `X₁` in degree `n + 1`; descending
induction on `n` starting from `B` concludes.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ComposableArrows

namespace DerivedCategory

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- The six-term homology sequence of the image of a distinguished triangle under a triangulated
functor to a derived category is exact. -/
lemma homologySequenceComposableArrows₅_mapTriangle_exact (F : C ⥤ DerivedCategory A)
    [F.CommShift ℤ] [F.IsTriangulated] {T : Triangle C} (hT : T ∈ distTriang C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    ((homologyFunctor A 0).homologySequenceComposableArrows₅
      (F.mapTriangle.obj T) n₀ n₁ h).Exact :=
  (homologyFunctor A 0).homologySequenceComposableArrows₅_exact _ (F.map_distinguished T hT) _ _ h

variable {F₁ F₂ : C ⥤ DerivedCategory A} [F₁.CommShift ℤ] [F₂.CommShift ℤ] [F₁.IsTriangulated]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ]

/-- The morphism between the six-term homology sequences of the images of a triangle `T` under
`F₁` and `F₂`, induced by `τ`. -/
noncomputable def homologySequenceComposableArrows₅Map (T : Triangle C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    (homologyFunctor A 0).homologySequenceComposableArrows₅ (F₁.mapTriangle.obj T) n₀ n₁ h ⟶
      (homologyFunctor A 0).homologySequenceComposableArrows₅ (F₂.mapTriangle.obj T) n₀ n₁ h :=
  let φ := (NatTrans.mapTriangle τ).app T
  let H (n : ℤ) := (homologyFunctor A 0).shift n
  have sq (n : ℤ) {X₁ X₂ Y₁ Y₂ : DerivedCategory A} {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂}
      {a : X₁ ⟶ Y₁} {b : X₂ ⟶ Y₂} (w : f ≫ b = a ≫ g) :
      (H n).map f ≫ (H n).map b = (H n).map a ≫ (H n).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  homMk₅ ((H n₀).map φ.hom₁) ((H n₀).map φ.hom₂) ((H n₀).map φ.hom₃) ((H n₁).map φ.hom₁)
    ((H n₁).map φ.hom₂) ((H n₁).map φ.hom₃) (sq n₀ φ.comm₁) (sq n₀ φ.comm₂)
    ((homologyFunctor A 0).homologySequenceδ_naturality φ n₀ n₁ h).symm
    (sq n₁ φ.comm₁) (sq n₁ φ.comm₂)

/-- The epimorphism half of the way-out step: for a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`,
the map `Hⁿ(τ X₃)` is an epimorphism if `Hⁿ(τ X₂)` and `Hⁿ⁺¹(τ X₁)` are epimorphisms and
`Hⁿ⁺¹(τ X₂)` is a monomorphism. -/
lemma epi_homologyFunctor_map_app_obj₃ {T : Triangle C} (hT : T ∈ distTriang C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) (h₂ : Epi ((homologyFunctor A n₀).map (τ.app T.obj₂)))
    (h₁ : Epi ((homologyFunctor A n₁).map (τ.app T.obj₁)))
    (h₂' : Mono ((homologyFunctor A n₁).map (τ.app T.obj₂))) :
    Epi ((homologyFunctor A n₀).map (τ.app T.obj₃)) :=
  Abelian.epi_of_epi_of_epi_of_mono'' (k := 1) (by lia)
    (homologySequenceComposableArrows₅_mapTriangle_exact F₁ hT n₀ n₁ h)
    (homologySequenceComposableArrows₅_mapTriangle_exact F₂ hT n₀ n₁ h)
    (homologySequenceComposableArrows₅Map τ T n₀ n₁ h) 1 2 3 4 rfl rfl rfl rfl h₂ h₁ h₂'

/-- The monomorphism half of the way-out step: for a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`, the map `Hⁿ(τ X₃)` is a monomorphism if `Hⁿ(τ X₁)` is an epimorphism
and `Hⁿ(τ X₂)` and `Hⁿ⁺¹(τ X₁)` are monomorphisms. -/
lemma mono_homologyFunctor_map_app_obj₃ {T : Triangle C} (hT : T ∈ distTriang C) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) (h₁ : Epi ((homologyFunctor A n₀).map (τ.app T.obj₁)))
    (h₂ : Mono ((homologyFunctor A n₀).map (τ.app T.obj₂)))
    (h₁' : Mono ((homologyFunctor A n₁).map (τ.app T.obj₁))) :
    Mono ((homologyFunctor A n₀).map (τ.app T.obj₃)) :=
  Abelian.mono_of_epi_of_mono_of_mono'' (k := 0) (by lia)
    (homologySequenceComposableArrows₅_mapTriangle_exact F₁ hT n₀ n₁ h)
    (homologySequenceComposableArrows₅_mapTriangle_exact F₂ hT n₀ n₁ h)
    (homologySequenceComposableArrows₅Map τ T n₀ n₁ h) 0 1 2 3 rfl rfl rfl rfl h₁ h₂ h₁'

/-- **Way-out argument.** Let `S` be a property of objects of `C` such that `F₁ X` and `F₂ X`
vanish above a common degree `B` for `X` in `S`, and such that every `X` in `S` is the third
object of a distinguished triangle `X₁ ⟶ P ⟶ X ⟶ X₁[1]` with `X₁` in `S` and `τ` an isomorphism
at `P`. Then `τ` is an isomorphism at every object of `S`. -/
theorem isIso_app_of_exists_distTriang (S : ObjectProperty C) (B : ℤ)
    (hB : ∀ X, S X → (F₁.obj X).IsLE B ∧ (F₂.obj X).IsLE B)
    (hS : ∀ X, S X → ∃ T ∈ distTriang C, T.obj₃ = X ∧ S T.obj₁ ∧ IsIso (τ.app T.obj₂))
    (X : C) (hX : S X) : IsIso (τ.app X) := by
  have key (k : ℕ) : ∀ X, S X → ∀ n : ℤ, B - k < n →
      IsIso ((homologyFunctor A n).map (τ.app X)) := by
    induction k with
    | zero =>
      intro X hX n hn
      obtain ⟨h₁, h₂⟩ := hB X hX
      exact isIso_of_source_target_iso_zero _
        (((F₁.obj X).isLE_iff B).1 h₁ n (by lia)).isoZero
        (((F₂.obj X).isLE_iff B).1 h₂ n (by lia)).isoZero
    | succ k ih =>
      -- the new degree is `n = B - k`
      have hepi : ∀ X, S X → Epi ((homologyFunctor A (B - k)).map (τ.app X)) := by
        intro X hX
        obtain ⟨T, hT, rfl, hT₁, hT₂⟩ := hS X hX
        have := ih _ hT₁ (B - k + 1) (by lia)
        exact epi_homologyFunctor_map_app_obj₃ τ hT (B - k) (B - k + 1) rfl inferInstance
          inferInstance inferInstance
      have hmono : ∀ X, S X → Mono ((homologyFunctor A (B - k)).map (τ.app X)) := by
        intro X hX
        obtain ⟨T, hT, rfl, hT₁, hT₂⟩ := hS X hX
        have := ih _ hT₁ (B - k + 1) (by lia)
        have := hepi _ hT₁
        exact mono_homologyFunctor_map_app_obj₃ τ hT (B - k) (B - k + 1) rfl inferInstance
          inferInstance inferInstance
      intro X hX n hn
      obtain hn | rfl : B - k < n ∨ n = B - k := by lia
      · exact ih X hX n hn
      · have := hepi X hX
        have := hmono X hX
        exact isIso_of_mono_of_epi _
  rw [isIso_iff]
  intro n
  exact key (B - n + 1).toNat X hX n (by lia)

end DerivedCategory
