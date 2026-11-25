/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs in filtered 2-colimits of monoidal closed categories

Let `c` be a cocone of categories (`CategoryTheory.CategoryCocone`) on a directed system of
monoidal closed categories `C i`, with monoidal transition functors `T h : C i ⥤ C j`, monoidal
functors `Φ i : C i ⥤ D` to a monoidal closed vertex `D` and monoidal isomorphisms
`T h ⋙ Φ j ≅ Φ i`. If `c` is a filtered 2-colimit (`CategoryCocone.IsFilteredTwoColimit`) and the
transition functors commute with internal homs, i.e. their comparison maps
`T [A, B] ⟶ [T A, T B]` (`Functor.LaxMonoidal.ihomComparison`) are isomorphisms, then so do the
functors `Φ i` (`CategoryTheory.CategoryCocone.isIso_ihomComparison_Φ`). No coherence between the
transition functors is used.

The proof is by Yoneda: writing `v` for the comparison map `Φ i [A, B] ⟶ [Φ i A, Φ i B]`, every
morphism to `[Φ i A, Φ i B]` from an object coming from a finite stage factors through `v`
(`CategoryTheory.CategoryCocone.exists_comp_ihomComparison_app_eq_of_obj`): by adjunction it is
a morphism `Φ (A ⊗ y) ⟶ Φ B`, which is defined at a finite stage. Composition with `v` is
injective on morphisms from such objects
(`CategoryTheory.CategoryCocone.eq_of_comp_ihomComparison_app_eq`): two morphisms with the same
composite become equal at a finite stage. Every object of `D` comes from a finite stage, so `v`
has a section which is also a retraction.

The general computations with comparison maps, along a monoidal natural isomorphism
`T ⋙ F' ≅ F`, are in the namespace `CategoryTheory.Functor.LaxMonoidal`.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory MonoidalClosed

variable {C C' D : Type*} [Category* C] [Category* C'] [Category* D] [MonoidalCategory C]
  [MonoidalCategory C'] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed C']
  [MonoidalClosed D]

/-- The transpose of `F g` followed by the comparison map `F [A, B] ⟶ [F A, F B]` is the
tensorator followed by `F` of the transpose of `g : y ⟶ [A, B]`. -/
lemma uncurry_map_comp_ihomComparison_app (F : C ⥤ D) [F.LaxMonoidal] {A B y : C}
    (g : y ⟶ (ihom A).obj B) :
    uncurry (F.map g ≫ (ihomComparison F A).app B) = μ F A y ≫ F.map (uncurry g) := by
  rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, μ_natural_right_assoc, ← F.map_comp,
    ← uncurry_eq]

/-- For a monoidal functor `F` and `g₁ g₂ : y ⟶ [A, B]`, the composites of `F g₁` and `F g₂`
with the comparison map `F [A, B] ⟶ [F A, F B]` agree if and only if `F` identifies the
transposes of `g₁` and `g₂`. -/
lemma map_comp_ihomComparison_app_eq_iff (F : C ⥤ D) [F.Monoidal] {A B y : C}
    (g₁ g₂ : y ⟶ (ihom A).obj B) :
    F.map g₁ ≫ (ihomComparison F A).app B =
        F.map g₂ ≫ (ihomComparison F A).app B ↔
      F.map (uncurry g₁) = F.map (uncurry g₂) := by
  rw [← uncurry_injective.eq_iff, uncurry_map_comp_ihomComparison_app,
    uncurry_map_comp_ihomComparison_app, cancel_epi]

/-- The comparison maps along a monoidal natural transformation `τ : T ⋙ F' ⟶ F`: after
transposition, composing `h : Y ⟶ F' (T [A, B])` with `τ` and the comparison map of `F` amounts
to composing it with `F'` of the comparison map of `T` and the comparison map of `F'`, up to
the components of `τ` at `A` and `B`. -/
lemma whiskerRight_comp_uncurry_comp_ihomComparison_app {T : C ⥤ C'} {F' : C' ⥤ D} {F : C ⥤ D}
    [T.LaxMonoidal] [F'.LaxMonoidal] [F.LaxMonoidal] (τ : T ⋙ F' ⟶ F) [NatTrans.IsMonoidal τ]
    {A B : C} {Y : D} (h : Y ⟶ F'.obj (T.obj ((ihom A).obj B))) :
    τ.app A ▷ Y ≫ uncurry (h ≫ τ.app _ ≫ (ihomComparison F A).app B) =
      uncurry (h ≫ F'.map ((ihomComparison T A).app B) ≫
        (ihomComparison F' (T.obj A)).app (T.obj B)) ≫ τ.app B := by
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_eq, ihomComparison_ev,
    ← whisker_exchange_assoc, ← tensorHom_def_assoc,
    ← NatTrans.IsMonoidal.tensor_assoc, ← τ.naturality, uncurry_natural_left, uncurry_eq,
    MonoidalCategory.whiskerLeft_comp_assoc, ihomComparison_ev]
  simp only [Category.assoc, Functor.comp_obj, μ_natural_right_assoc, ← F'.map_comp_assoc,
    ihomComparison_ev, comp_μ]
  simp

/-- Along a monoidal natural isomorphism `τ : T ⋙ F' ≅ F`, two morphisms to `F' (T [A, B])`
have the same composite with `τ` and the comparison map of `F` if and only if they have the same
composite with `F'` of the comparison map of `T` and the comparison map of `F'`. -/
lemma comp_app_comp_ihomComparison_app_eq_iff {T : C ⥤ C'} {F' : C' ⥤ D} {F : C ⥤ D}
    [T.LaxMonoidal] [F'.LaxMonoidal] [F.LaxMonoidal] (τ : T ⋙ F' ≅ F)
    [NatTrans.IsMonoidal τ.hom] {A B : C} {Y : D} (h₁ h₂ : Y ⟶ F'.obj (T.obj ((ihom A).obj B))) :
    h₁ ≫ τ.hom.app _ ≫ (ihomComparison F A).app B =
        h₂ ≫ τ.hom.app _ ≫ (ihomComparison F A).app B ↔
      h₁ ≫ F'.map ((ihomComparison T A).app B) ≫
          (ihomComparison F' (T.obj A)).app (T.obj B) =
        h₂ ≫ F'.map ((ihomComparison T A).app B) ≫
          (ihomComparison F' (T.obj A)).app (T.obj B) := by
  rw [← uncurry_injective.eq_iff, ← cancel_epi (τ.hom.app A ▷ Y),
    whiskerRight_comp_uncurry_comp_ihomComparison_app,
    whiskerRight_comp_uncurry_comp_ihomComparison_app, cancel_mono, uncurry_injective.eq_iff]

/-- Along a monoidal natural isomorphism `τ : T ⋙ F' ≅ F` with the comparison map
`T [A, B] ⟶ [T A, T B]` an isomorphism: if every morphism from `Y` to `[F' (T A), F' (T B)]`
factors through the comparison map of `F'`, then every morphism from `Y` to `[F A, F B]`
factors through the comparison map of `F`. -/
lemma exists_comp_ihomComparison_app_eq_of_iso {T : C ⥤ C'} {F' : C' ⥤ D} {F : C ⥤ D}
    [T.LaxMonoidal] [F'.LaxMonoidal] [F.LaxMonoidal] (τ : T ⋙ F' ≅ F)
    [NatTrans.IsMonoidal τ.hom] {A B : C} [IsIso ((ihomComparison T A).app B)] {Y : D}
    (hY : ∀ g : Y ⟶ (ihom (F'.obj (T.obj A))).obj (F'.obj (T.obj B)),
      ∃ f, f ≫ (ihomComparison F' (T.obj A)).app (T.obj B) = g)
    (g : Y ⟶ (ihom (F.obj A)).obj (F.obj B)) :
    ∃ f, f ≫ (ihomComparison F A).app B = g := by
  obtain ⟨f, hf⟩ := hY (curry (τ.hom.app A ▷ Y ≫ uncurry g ≫ τ.inv.app B))
  refine ⟨(f ≫ CategoryTheory.inv (F'.map ((ihomComparison T A).app B))) ≫
    τ.hom.app _, ?_⟩
  apply uncurry_injective
  rw [← cancel_epi (τ.hom.app A ▷ Y), Category.assoc,
    whiskerRight_comp_uncurry_comp_ihomComparison_app]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [hf, uncurry_curry]
  simp

/-- Along a monoidal natural isomorphism `τ : T ⋙ F' ≅ F` with the comparison map
`T [A, B] ⟶ [T A, T B]` an isomorphism: a morphism `g : F y ⟶ [F A, F B]` whose transpose is,
up to the tensorator and `τ`, the image under `F'` of `x : T (A ⊗ y) ⟶ T B`, factors through
the comparison map of `F`, explicitly. -/
lemma comp_ihomComparison_app_eq_of_uncurry_eq {T : C ⥤ C'} {F' : C' ⥤ D} {F : C ⥤ D}
    [T.LaxMonoidal] [F'.LaxMonoidal] [F.LaxMonoidal] (τ : T ⋙ F' ≅ F)
    [NatTrans.IsMonoidal τ.hom] {A B y : C} [IsIso ((ihomComparison T A).app B)]
    (x : T.obj (A ⊗ y) ⟶ T.obj B) (g : F.obj y ⟶ (ihom (F.obj A)).obj (F.obj B))
    (hg : uncurry g = μ F A y ≫ τ.inv.app _ ≫ F'.map x ≫ τ.hom.app B) :
    (τ.inv.app y ≫ F'.map (curry (μ T A y ≫ x) ≫
      CategoryTheory.inv ((ihomComparison T A).app B)) ≫ τ.hom.app _) ≫
        (ihomComparison F A).app B = g := by
  apply uncurry_injective
  rw [Category.assoc, Category.assoc, ← Category.assoc (τ.inv.app y)]
  rw [← cancel_epi (τ.hom.app A ▷ _), whiskerRight_comp_uncurry_comp_ihomComparison_app, hg]
  simp only [Category.assoc, ← F'.map_comp_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [uncurry_natural_left, uncurry_map_comp_ihomComparison_app, uncurry_curry,
    NatTrans.IsMonoidal.tensor_assoc]
  simp [tensorHom_def, ← comp_whiskerRight_assoc]

end CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.CategoryCocone

open MonoidalCategory MonoidalClosed Functor.LaxMonoidal

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, MonoidalCategory (C i)] [∀ i, MonoidalClosed (C i)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [MonoidalClosed D]
  (c : CategoryCocone C D) [∀ i, (c.Φ i).Monoidal] [∀ (i j : I) (h : i ≤ j), (c.T h).Monoidal]
  [∀ (i j : I) (h : i ≤ j), NatTrans.IsMonoidal (c.iso h).hom]

omit [∀ (i j : I) (h : i ≤ j), NatTrans.IsMonoidal (c.iso h).hom] in
/-- In a filtered 2-colimit whose transition functors commute with internal homs, if
`g₁ g₂ : y ⟶ [A, B]` at stage `m` have the same composite `Φ m g ≫ v` with the comparison map
`v : Φ m [A, B] ⟶ [Φ m A, Φ m B]`, then `Φ m g₁ = Φ m g₂`. -/
lemma map_eq_map_of_map_comp_ihomComparison_app_eq (hc : c.IsFilteredTwoColimit)
    (hT : ∀ (i j : I) (h : i ≤ j) (A : C i), IsIso (ihomComparison (c.T h) A))
    {m : I} {y A B : C m} (g₁ g₂ : y ⟶ (ihom A).obj B)
    (hg : (c.Φ m).map g₁ ≫ (ihomComparison (c.Φ m) A).app B =
      (c.Φ m).map g₂ ≫ (ihomComparison (c.Φ m) A).app B) :
    (c.Φ m).map g₁ = (c.Φ m).map g₂ := by
  rw [map_comp_ihomComparison_app_eq_iff] at hg
  obtain ⟨m', h, hTg⟩ := hc.homInj m _ _ _ _ hg
  have := hT _ _ h A
  rw [← map_comp_ihomComparison_app_eq_iff, cancel_mono] at hTg
  rw [← NatIso.naturality_1 (c.iso h) g₁, ← NatIso.naturality_1 (c.iso h) g₂, Functor.comp_map,
    Functor.comp_map, hTg]

/-- In a filtered 2-colimit whose transition functors commute with internal homs, if
`g : y ⟶ [A, B]` at stage `m` and `f : Φ m y ⟶ Φ m [A, B]` have the same composite with the
comparison map `v : Φ m [A, B] ⟶ [Φ m A, Φ m B]`, then `Φ m g = f`. -/
lemma map_eq_of_map_comp_ihomComparison_app_eq (hc : c.IsFilteredTwoColimit)
    (hT : ∀ (i j : I) (h : i ≤ j) (A : C i), IsIso (ihomComparison (c.T h) A))
    {m : I} {y A B : C m} (g : y ⟶ (ihom A).obj B)
    (f : (c.Φ m).obj y ⟶ (c.Φ m).obj ((ihom A).obj B))
    (hf : (c.Φ m).map g ≫ (ihomComparison (c.Φ m) A).app B =
      f ≫ (ihomComparison (c.Φ m) A).app B) :
    (c.Φ m).map g = f := by
  obtain ⟨m', h, h', x, rfl⟩ := hc.homSurj m m y _ f
  obtain rfl : h = h' := rfl
  have := hT _ _ h A
  rw [← NatIso.naturality_1 (c.iso h) g] at hf ⊢
  simp only [Category.assoc, cancel_epi] at hf ⊢
  rw [Functor.comp_map, comp_app_comp_ihomComparison_app_eq_iff, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc] at hf
  have := map_eq_map_of_map_comp_ihomComparison_app_eq c hc hT _ _ hf
  rw [Functor.map_comp, Functor.map_comp, cancel_mono] at this
  rw [Functor.comp_map, this]

/-- In a filtered 2-colimit whose transition functors commute with internal homs, composition
with the comparison map `v : Φ k [A, B] ⟶ [Φ k A, Φ k B]` is injective on morphisms from an
object `Φ k y` coming from the same stage. -/
lemma eq_of_comp_ihomComparison_app_eq (hc : c.IsFilteredTwoColimit)
    (hT : ∀ (i j : I) (h : i ≤ j) (A : C i), IsIso (ihomComparison (c.T h) A))
    {k : I} {y A B : C k} (f f' : (c.Φ k).obj y ⟶ (c.Φ k).obj ((ihom A).obj B))
    (hf : f ≫ (ihomComparison (c.Φ k) A).app B =
      f' ≫ (ihomComparison (c.Φ k) A).app B) :
    f = f' := by
  obtain ⟨m, h, h', x, rfl⟩ := hc.homSurj k k y _ f
  obtain rfl : h = h' := rfl
  have := hT _ _ h A
  obtain ⟨f'', rfl⟩ : ∃ f'', f' = (c.iso h).inv.app y ≫ f'' ≫ (c.iso h).hom.app _ :=
    ⟨(c.iso h).hom.app y ≫ f' ≫ (c.iso h).inv.app _, by simp⟩
  simp only [Category.assoc, cancel_epi] at hf
  rw [comp_app_comp_ihomComparison_app_eq_iff, ← Functor.map_comp_assoc,
    ← Category.assoc f''] at hf
  have := map_eq_of_map_comp_ihomComparison_app_eq c hc hT _ _ hf
  rw [Functor.map_comp, cancel_mono] at this
  rw [this]

/-- In a filtered 2-colimit whose transition functors commute with internal homs, every
morphism from `Φ k y` to `[Φ k A, Φ k B]` factors through the comparison map
`Φ k [A, B] ⟶ [Φ k A, Φ k B]`. -/
lemma exists_comp_ihomComparison_app_eq_of_obj (hc : c.IsFilteredTwoColimit)
    (hT : ∀ (i j : I) (h : i ≤ j) (A : C i), IsIso (ihomComparison (c.T h) A))
    {k : I} {y A B : C k} (g : (c.Φ k).obj y ⟶ (ihom ((c.Φ k).obj A)).obj ((c.Φ k).obj B)) :
    ∃ f, f ≫ (ihomComparison (c.Φ k) A).app B = g := by
  obtain ⟨m, h, h', x, hx⟩ :=
    hc.homSurj k k (A ⊗ y) B (CategoryTheory.inv (μ (c.Φ k) A y) ≫ uncurry g)
  obtain rfl : h = h' := rfl
  have := hT _ _ h A
  exact ⟨_, comp_ihomComparison_app_eq_of_uncurry_eq (c.iso h) x g (by simp [← hx])⟩

/-- If the transition functors of a filtered 2-colimit of monoidal closed categories commute with
internal homs, so do the functors to the vertex. -/
theorem isIso_ihomComparison_Φ [IsDirected I (· ≤ ·)] (hc : c.IsFilteredTwoColimit)
    (hT : ∀ (i j : I) (h : i ≤ j) (A : C i),
      IsIso (Functor.LaxMonoidal.ihomComparison (c.T h) A))
    (i : I) (A : C i) : IsIso (Functor.LaxMonoidal.ihomComparison (c.Φ i) A) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  obtain ⟨j, y, ⟨e⟩⟩ := hc.essSurjObj ((ihom ((c.Φ i).obj A)).obj ((c.Φ i).obj B))
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have := hT _ _ hik A
  obtain ⟨s, hs⟩ := exists_comp_ihomComparison_app_eq_of_iso (c.iso hik) (fun g ↦ by
    obtain ⟨f, hf⟩ := exists_comp_ihomComparison_app_eq_of_obj c hc hT
      ((c.iso hjk).hom.app y ≫ e.hom ≫ g)
    exact ⟨e.inv ≫ (c.iso hjk).inv.app y ≫ f, by simp [hf]⟩) (𝟙 _)
  exact ⟨s, eq_of_comp_ihomComparison_app_eq c hc hT _ _ (by simp [hs]), hs⟩

end CategoryTheory.CategoryCocone
