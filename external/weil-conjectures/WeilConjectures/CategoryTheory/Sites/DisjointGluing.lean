/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Gluing morphisms of sheaves over disjoint covering families

A family `fᵢ : Uᵢ ⟶ X` is disjoint (`CategoryTheory.Presieve.IsDisjointFamily`) if the `fᵢ`
are monomorphisms and any object mapping compatibly to two distinct members is covered by the
empty sieve (e.g. a decomposition of a scheme into disjoint open and closed pieces). Families of
sections of a sheaf of types over such a family are automatically compatible, so
morphisms and isomorphisms of sheaves glue with no condition on overlaps.

- `Presieve.IsDisjointFamily.existsUnique_hom`, `Presieve.IsDisjointFamily.exists_iso`:
  gluing over a disjoint covering family of `X`, for the restrictions to `J.over X`;
- `Presieve.IsDisjointFamily.existsUnique_hom_of_isTerminal`,
  `Presieve.IsDisjointFamily.exists_iso_of_isTerminal`: global versions when `X` is
  terminal; e.g. a sheaf isomorphic to a constant sheaf `C(M)` on each piece is `≅ C(M)`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Opposite Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- On an object covered by the empty sieve, a sheaf of types has at most one section. -/
lemma Presieve.subsingleton_of_bot_mem {P : Cᵒᵖ ⥤ Type*} (hP : Presheaf.IsSheaf J P) {Z : C}
    (hZ : ⊥ ∈ J Z) : Subsingleton (P.obj (op Z)) :=
  ⟨fun _ _ ↦ ((isSheaf_iff_isSheaf_of_type J P).1 hP _ hZ).isSeparatedFor.ext
    fun _ _ h ↦ h.elim⟩

variable {X : C} {ι : Type*} {U : ι → C} (f : ∀ i, U i ⟶ X)

/-- A family `fᵢ : Uᵢ ⟶ X` is **disjoint** if the `fᵢ` are monomorphisms and any object mapping
compatibly to two distinct `Uᵢ`, `Uⱼ` is covered by the empty sieve, e.g. a decomposition
`X = ⊔ Uᵢ` into disjoint open (and closed) pieces. -/
structure Presieve.IsDisjointFamily (J : GrothendieckTopology C) : Prop where
  mono (i : ι) : Mono (f i)
  bot_mem (i j : ι) (hij : i ≠ j) {Z : C} (a : Z ⟶ U i) (b : Z ⟶ U j) (h : a ≫ f i = b ≫ f j) :
    ⊥ ∈ J Z

variable {f}

/-- Any family of sections of a sheaf of types over the members of a disjoint family is
compatible. -/
lemma Presieve.IsDisjointFamily.compatible (hf : Presieve.IsDisjointFamily f J)
    {P : Cᵒᵖ ⥤ Type*} (hP : Presheaf.IsSheaf J P) (x : ∀ i, P.obj (op (U i))) :
    Presieve.Arrows.Compatible P f x := by
  intro i j Z a b h
  by_cases hij : i = j
  · subst hij
    have := hf.mono i
    rw [cancel_mono] at h
    rw [h]
  · have := Presieve.subsingleton_of_bot_mem hP (hf.bot_mem i j hij a b h)
    exact Subsingleton.elim _ _

variable {A : Type u'} [Category.{v'} A]

/-- **Gluing morphisms of sheaves over a disjoint covering family**: morphisms
`F|_{Uᵢ} ⟶ G|_{Uᵢ}` glue uniquely to a morphism `F|_X ⟶ G|_X`, with no compatibility
condition. -/
lemma Presieve.IsDisjointFamily.existsUnique_hom (hf : Presieve.IsDisjointFamily f J)
    (hcov : Sieve.ofArrows U f ∈ J X) (F G : Sheaf J A) (φ : ∀ i, F.over (U i) ⟶ G.over (U i)) :
    ∃! ψ : F.over X ⟶ G.over X, ∀ i, (J.overMapPullback A (f i)).map ψ = φ i := by
  have h := (sheafHom F G).2
  have h' := (isSheaf_iff_isSheaf_of_type J _).1 h _ hcov
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at h'
  exact h' φ (hf.compatible h φ)

/-- **Gluing isomorphisms of sheaves over a disjoint covering family**: if `F` and `G` are
isomorphic on each member `Uᵢ` of a disjoint covering family of `X`, they are isomorphic on `X`,
through an isomorphism restricting to the given ones. -/
lemma Presieve.IsDisjointFamily.exists_iso (hf : Presieve.IsDisjointFamily f J)
    (hcov : Sieve.ofArrows U f ∈ J X) (F G : Sheaf J A) (e : ∀ i, F.over (U i) ≅ G.over (U i)) :
    ∃ e' : F.over X ≅ G.over X, ∀ i, (J.overMapPullback A (f i)).map e'.hom = (e i).hom := by
  obtain ⟨φ, hφ, -⟩ := hf.existsUnique_hom hcov F G fun i ↦ (e i).hom
  obtain ⟨ψ, hψ, -⟩ := hf.existsUnique_hom hcov G F fun i ↦ (e i).inv
  have h₁ : φ ≫ ψ = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hf.existsUnique_hom hcov F F fun i ↦ 𝟙 _
    refine (hχ _ fun i ↦ ?_).trans (hχ _ fun i ↦ ?_).symm
    · rw [Functor.map_comp, hφ, hψ, Iso.hom_inv_id]
      rfl
    · exact Functor.map_id _ _
  have h₂ : ψ ≫ φ = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hf.existsUnique_hom hcov G G fun i ↦ 𝟙 _
    refine (hχ _ fun i ↦ ?_).trans (hχ _ fun i ↦ ?_).symm
    · rw [Functor.map_comp, hφ, hψ, Iso.inv_hom_id]
      rfl
    · exact Functor.map_id _ _
  exact ⟨⟨φ, ψ, h₁, h₂⟩, hφ⟩

/-- The sections of a presheaf of types over a category with a terminal object `T` are
determined by their value at `T`. -/
lemma Functor.sections_ext_of_isTerminal {P : Cᵒᵖ ⥤ Type*} {T : C} (hT : IsTerminal T)
    {s t : P.sections} (h : s.1 (op T) = t.1 (op T)) : s = t := by
  refine Subtype.ext (funext fun Y ↦ ?_)
  rw [← s.2 (hT.from Y.unop).op, ← t.2 (hT.from Y.unop).op, h]

/-- The section of a presheaf of types over a category with a terminal object `T` extending
an element of `P(T)`. -/
def Functor.sectionOfIsTerminal {P : Cᵒᵖ ⥤ Type*} {T : C} (hT : IsTerminal T)
    (x : P.obj (op T)) : P.sections :=
  ⟨fun Y ↦ P.map (hT.from Y.unop).op x, fun {Y Y'} g ↦ by
    dsimp only
    rw [← Functor.map_comp_apply, show (hT.from Y.unop).op ≫ g = (hT.from Y'.unop).op from
      Quiver.Hom.unop_inj (hT.hom_ext _ _)]⟩

/-- **Gluing morphisms of sheaves over a disjoint covering family of the terminal object**:
morphisms `F|_{Uᵢ} ⟶ G|_{Uᵢ}` glue uniquely to a morphism `F ⟶ G`. -/
lemma Presieve.IsDisjointFamily.existsUnique_hom_of_isTerminal
    (hf : Presieve.IsDisjointFamily f J) (hX : IsTerminal X) (hcov : Sieve.ofArrows U f ∈ J X)
    (F G : Sheaf J A) (φ : ∀ i, F.over (U i) ⟶ G.over (U i)) :
    ∃! ψ : F ⟶ G, ∀ i, (J.overPullback A (U i)).map ψ = φ i := by
  obtain ⟨ψ₀, hψ₀, hu⟩ := hf.existsUnique_hom hcov F G φ
  let e := sheafHomSectionsEquiv F G
  let s := Functor.sectionOfIsTerminal hX (P := (sheafHom F G).obj) ψ₀
  have key (ψ : F ⟶ G) (i : ι) : (J.overPullback A (U i)).map ψ =
      (sheafHom F G).obj.map (f i).op ((e.symm ψ).1 (op X)) := by
    rw [(e.symm ψ).2 (f i).op]
    rfl
  refine ⟨e s, fun i ↦ ?_, fun ψ hψ ↦ e.symm.injective ?_⟩
  · rw [key, Equiv.symm_apply_apply, ← hψ₀ i]
    change (sheafHom F G).obj.map _ ((sheafHom F G).obj.map _ ψ₀) = _
    rw [← Functor.map_comp_apply, ← op_comp, hX.hom_ext (f i ≫ hX.from X) (f i)]
    rfl
  · rw [Equiv.symm_apply_apply]
    refine Functor.sections_ext_of_isTerminal hX ?_
    refine (hu _ fun i ↦ ?_).trans ?_
    · rw [← hψ i, key]
      rfl
    · change ψ₀ = (sheafHom F G).obj.map (hX.from X).op ψ₀
      rw [hX.hom_ext (hX.from X) (𝟙 X), op_id, Functor.map_id_apply]

/-- **Gluing isomorphisms of sheaves over a disjoint covering family of the terminal object**:
if `F` and `G` are isomorphic on each member `Uᵢ` of a disjoint covering family of the terminal
object (e.g. `F` is isomorphic to a constant sheaf `C(M)` on each piece of a decomposition
into disjoint open and closed pieces), then `F ≅ G`. -/
lemma Presieve.IsDisjointFamily.exists_iso_of_isTerminal (hf : Presieve.IsDisjointFamily f J)
    (hX : IsTerminal X) (hcov : Sieve.ofArrows U f ∈ J X) (F G : Sheaf J A)
    (e : ∀ i, F.over (U i) ≅ G.over (U i)) :
    ∃ e' : F ≅ G, ∀ i, (J.overPullback A (U i)).map e'.hom = (e i).hom := by
  obtain ⟨φ, hφ, -⟩ := hf.existsUnique_hom_of_isTerminal hX hcov F G fun i ↦ (e i).hom
  obtain ⟨ψ, hψ, -⟩ := hf.existsUnique_hom_of_isTerminal hX hcov G F fun i ↦ (e i).inv
  have h₁ : φ ≫ ψ = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hf.existsUnique_hom_of_isTerminal hX hcov F F fun i ↦ 𝟙 _
    refine (hχ _ fun i ↦ ?_).trans (hχ _ fun i ↦ ?_).symm
    · rw [Functor.map_comp, hφ, hψ, Iso.hom_inv_id]
    · exact Functor.map_id _ _
  have h₂ : ψ ≫ φ = 𝟙 _ := by
    obtain ⟨χ, -, hχ⟩ := hf.existsUnique_hom_of_isTerminal hX hcov G G fun i ↦ 𝟙 _
    refine (hχ _ fun i ↦ ?_).trans (hχ _ fun i ↦ ?_).symm
    · rw [Functor.map_comp, hφ, hψ, Iso.inv_hom_id]
    · exact Functor.map_id _ _
  exact ⟨⟨φ, ψ, h₁, h₂⟩, hφ⟩

end CategoryTheory
