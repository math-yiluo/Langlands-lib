/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions



/-! # Higher direct image transition compatibility

Source: Stacks Project, Tags 09Z1 and 03Q8, canonical comparison maps.
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

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

/-- The transition is natural in its coefficient sheaf.
Source: Stacks Tag 09Z1, canonical comparison maps; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-naturality).

Proof: write the derived transition as the composite natural transformation formed by
the h' adjunction unit, the pullback composition comparison, and pullback of the h
adjunction counit. Each is natural, so its naturality square commutes for F[0]→G[0].
The single-complex comparison is itself natural, and applying Rh'_* and homology
preserves the commuting square. This gives the displayed equality. For identity maps
it is reflexivity, for zero maps it is the zero equality by additivity, and the argument
uses no geometric or cohomological bound assumptions.
-/
theorem higher_direct_image_transition_naturality
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S)
    (w : a ≫ h = h') (q : ℤ)
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : F ⟶ G) :
    (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f)) ≫
      higherDirectImageTransition Λ a h h' w q G =
    higherDirectImageTransition Λ a h h' w q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((a)^*[ModuleCat.{u + 1} Λ]).map f))) := by
  subst h'
  let Rh := R+((h)_*[ModuleCat.{u + 1} Λ])
  let Rh' := R+((a ≫ h)_*[ModuleCat.{u + 1} Λ])
  let La := D+((a)^*[ModuleCat.{u + 1} Λ])
  let c : D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]) ≅
      D+((h)^*[ModuleCat.{u + 1} Λ]) ⋙ La :=
    eqToIso (by rfl) ≪≫ upperStarPlusComp (ModuleCat.{u + 1} Λ) a h
  have hn (K L : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (k : K ⟶ L) :
      Rh.map k ≫ lowerStarPlusTransition Λ a h (a ≫ h) rfl L =
        lowerStarPlusTransition Λ a h (a ≫ h) rfl K ≫ Rh'.map (La.map k) := by
    exact transition_naturality D+((h)^*[ModuleCat.{u + 1} Λ]) Rh
      D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]) Rh' La
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h)
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)) c.hom
      (lowerStarPlusTransition Λ a h (a ≫ h) rfl) (fun _ => rfl) k
  exact coefficient_transition_naturality (DerivedCategory.Plus.singleFunctor _ 0)
    La (((a)^*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.singleFunctor _ 0)
    Rh Rh' (DerivedCategory.Plus.homologyFunctor _ q)
    (lowerStarPlusTransition Λ a h (a ≫ h) rfl) hn
    ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom) f

end AlgebraicGeometry.Etale
