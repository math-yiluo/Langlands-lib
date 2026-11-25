/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition

/-! # Coefficient naturality of target transitions -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X T : Scheme.{u}}

private lemma transition_naturality
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) (R : D ⥤ C) (L' : C ⥤ E) (R' : E ⥤ C) (A : D ⥤ E)
    (adj : L ⊣ R) (adj' : L' ⊣ R') (c : L' ⟶ L ⋙ A)
    (t : ∀ K : D, R.obj K ⟶ R'.obj (A.obj K))
    (ht : ∀ K, t K = adj'.unit.app (R.obj K) ≫
      R'.map (c.app (R.obj K) ≫ A.map (adj.counit.app K)))
    {K M : D} (k : K ⟶ M) :
    R.map k ≫ t M = t K ≫ R'.map (A.map k) := by
  rw [ht K, ht M]
  have hu := adj'.unit.naturality (R.map k)
  have hc := c.naturality (R.map k)
  have he := adj.counit.naturality k
  simp only [Functor.id_map, Functor.comp_map] at hu hc he
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← R'.map_comp, ← R'.map_comp]
  congr 1
  rw [← Category.assoc, hc]
  simp only [Category.assoc]
  rw [← A.map_comp, ← A.map_comp, he]

private lemma coefficient_transition_naturality
    {C D E T U : Type*} [Category* C] [Category* D] [Category* E]
    [Category* T] [Category* U]
    (S : C ⥤ D) (A : D ⥤ E) (B : C ⥤ E) (R : D ⥤ T) (R' : E ⥤ T)
    (H : T ⥤ U) (t : ∀ K : D, R.obj K ⟶ R'.obj (A.obj K))
    (ht : ∀ (K M : D) (k : K ⟶ M), R.map k ≫ t M = t K ≫ R'.map (A.map k))
    (c : S ⋙ A ⟶ B) {F G : C} (f : F ⟶ G) :
    H.map (R.map (S.map f)) ≫ H.map (t (S.obj G) ≫ R'.map (c.app G)) =
      H.map (t (S.obj F) ≫ R'.map (c.app F)) ≫ H.map (R'.map (B.map f)) := by
  have hc := c.naturality f
  simp only [Functor.comp_map] at hc
  rw [← H.map_comp, ← H.map_comp]
  congr 1
  rw [← Category.assoc, ht, Category.assoc, ← R'.map_comp, hc, R'.map_comp,
    Category.assoc]

private lemma coefficient_transition_naturality_raw
    {C D₀ D E T U I : Type*} [Category* C] [Category* D₀] [Category* D]
    [Category* E] [Category* T] [Category* U]
    (S : C ⥤ D₀) (L : D₀ ⥤ D) (A : D ⥤ E) (P : I → D₀ ⥤ E) (N : D₀ ⥤ E)
    (B : C ⥤ E) (R : D ⥤ T) (R' : E ⥤ T) (H : T ⥤ U)
    (t : ∀ K : D, R.obj K ⟶ R'.obj (A.obj K))
    (ht : ∀ (K M : D) (k : K ⟶ M), R.map k ≫ t M = t K ≫ R'.map (A.map k))
    (i j : I) (w : i = j) (c₁ : L ⋙ A ⟶ P i) (c₂ : P j ⟶ N) (c₃ : S ⋙ N ⟶ B)
    {F G : C} (f : F ⟶ G) :
    H.map (R.map (L.map (S.map f))) ≫
      H.map (t (L.obj (S.obj G)) ≫ R'.map
        (c₁.app (S.obj G) ≫ eqToHom (congrArg (fun k ↦ (P k).obj (S.obj G)) w) ≫
          c₂.app (S.obj G) ≫ c₃.app G)) =
    H.map (t (L.obj (S.obj F)) ≫ R'.map
      (c₁.app (S.obj F) ≫ eqToHom (congrArg (fun k ↦ (P k).obj (S.obj F)) w) ≫
        c₂.app (S.obj F) ≫ c₃.app F)) ≫ H.map (R'.map (B.map f)) := by
  subst j
  let c := Functor.whiskerLeft S (c₁ ≫ c₂) ≫ c₃
  simpa only [c, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_refl,
    Category.id_comp, Functor.comp_obj, Functor.comp_map, Category.assoc] using
    coefficient_transition_naturality (S ⋙ L) A B R R' H t ht c f

/-- Coefficient naturality of the canonical target transition.
Source: Stacks Project, Tag 0F07, naturality in the closed–open argument.
(blueprint: lem-sbc-target-transition-coefficient-naturality).

Proof: The derived transition is formed from the adjunction unit, pullback comparison,
and adjunction counit, each natural in its coefficient complex. The pullback comparisons
and the comparison with a single complex are natural transformations. Compose their
naturality squares and apply derived pushforward followed by degree-q homology. This
argument applies to arbitrary coefficient maps and every integer degree.
-/
lemma target_transition_naturality
    {Y Y' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    {T' : Scheme.{u}} (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (α : F ⟶ G) :
    (baseChangeTargetFunctor Λ e h q).map α ≫
        baseChangeTargetTransition Λ e h q π a e' h' wa wh G =
      baseChangeTargetTransition Λ e h q π a e' h' wa wh F ≫
        (baseChangeTargetFunctor Λ e' h' q).map
          (((π)^*[ModuleCat.{u + 1} Λ]).map α) := by
  subst h'
  let Rh := R+((h)_*[ModuleCat.{u + 1} Λ])
  let Rh' := R+((a ≫ h)_*[ModuleCat.{u + 1} Λ])
  let La := D+((a)^*[ModuleCat.{u + 1} Λ])
  let c₀ : D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]) ≅
      D+((h)^*[ModuleCat.{u + 1} Λ]) ⋙ La :=
    eqToIso (by rfl) ≪≫ upperStarPlusComp (ModuleCat.{u + 1} Λ) a h
  have hn (K L : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (k : K ⟶ L) :
      Rh.map k ≫ lowerStarPlusTransition Λ a h (a ≫ h) rfl L =
        lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫ Rh'.map (La.map k) := by
    exact transition_naturality D+((h)^*[ModuleCat.{u + 1} Λ]) Rh
      D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]) Rh' La
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h)
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)) c₀.hom
      (lowerStarPlusTransition Λ a h (a ≫ h) rfl) (fun _ ↦ rfl) k
  exact coefficient_transition_naturality_raw
    (DerivedCategory.Plus.singleFunctor _ 0) D+((e)^*[ModuleCat.{u + 1} Λ]) La
    (fun k : Y' ⟶ T ↦ D+((k)^*[ModuleCat.{u + 1} Λ]))
    (D+((π)^*[ModuleCat.{u + 1} Λ]) ⋙ D+((e')^*[ModuleCat.{u + 1} Λ]))
    ((((π)^*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.singleFunctor _ 0) ⋙
      D+((e')^*[ModuleCat.{u + 1} Λ]))
    Rh Rh' (DerivedCategory.Plus.homologyFunctor _ q)
    (lowerStarPlusTransition Λ a h (a ≫ h) rfl) hn
    (a ≫ e) (e' ≫ π) wa
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom
    (Functor.whiskerRight
      (((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom
      D+((e')^*[ModuleCat.{u + 1} Λ])) α

end AlgebraicGeometry.Etale
