/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Existence of homotopy limits of towers, and exact functors

Let `F : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category in which the product `∏ₙ Fₙ`
exists. Completing `1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` (`CategoryTheory.Pretriangulated.towerShift`) to a
distinguished triangle gives a homotopy limit cone `R lim F` of `F`
(`CategoryTheory.Pretriangulated.homotopyLimitCone`). It is a choice: homotopy limits are only
unique up to non-unique isomorphism.

A triangulated functor commuting with countable products sends homotopy limit cones to homotopy
limit cones (`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`), so it commutes with `R lim`
up to an isomorphism compatible with the legs
(`CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_map`, blueprint
`lem-cbc-exact-functor-rlim`).

## Main definitions

- `CategoryTheory.Pretriangulated.homotopyLimitCone`: a chosen homotopy limit cone of a tower.
- `CategoryTheory.Pretriangulated.homotopyLimitLift`: a lift of a cone into it.
- `CategoryTheory.Pretriangulated.homotopyLimitMap`: a map of chosen homotopy limits induced by a
  morphism of towers, the first component of a morphism of Milnor triangles; it is a choice.

## Main statements

- `CategoryTheory.Pretriangulated.isHomotopyLimit_homotopyLimitCone`: it is a homotopy limit.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_map`: exact functors commuting with
  countable products commute with homotopy limits of towers.
- `CategoryTheory.Pretriangulated.isIso_homotopyLimitMap`: an isomorphism of towers induces an
  isomorphism of the chosen homotopy limits.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Existence

variable (F : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ ↦ F.obj (op n)]

/-- The transition endomorphism `t` of the chosen product `∏ₙ Fₙ` of a tower. -/
noncomputable abbrev piTowerShift :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  towerShift (productIsProduct fun n : ℕ ↦ F.obj (op n))

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc]
lemma piTowerShift_π (n : ℕ) :
    piTowerShift F ≫ Pi.π _ n = Pi.π _ (n + 1) ≫ F.map (homOfLE n.le_succ).op :=
  Fan.IsLimit.fac _ _ n

lemma exists_distTriang_sub_piTowerShift :
    ∃ (X : C) (f : X ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
      (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f (𝟙 _ - piTowerShift F) δ ∈ distTriang C :=
  distinguished_cocone_triangle₁ _

/-- The point of the chosen homotopy limit `R lim F` of a tower: a fibre of
`1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`. -/
noncomputable def homotopyLimit : C :=
  (exists_distTriang_sub_piTowerShift F).choose

/-- The map `R lim F ⟶ ∏ₙ Fₙ` of the chosen Milnor triangle. -/
noncomputable def homotopyLimitι : homotopyLimit F ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n) :=
  (exists_distTriang_sub_piTowerShift F).choose_spec.choose

lemma exists_distTriang_homotopyLimitι :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ (homotopyLimit F)⟦(1 : ℤ)⟧,
      Triangle.mk (homotopyLimitι F) (𝟙 _ - piTowerShift F) δ ∈ distTriang C :=
  (exists_distTriang_sub_piTowerShift F).choose_spec.choose_spec

lemma homotopyLimitι_comp_sub_piTowerShift :
    homotopyLimitι F ≫ (𝟙 _ - piTowerShift F) = 0 := by
  obtain ⟨δ, hT⟩ := exists_distTriang_homotopyLimitι F
  exact comp_distTriang_mor_zero₁₂ _ hT

lemma homotopyLimitι_π_succ (n : ℕ) :
    homotopyLimitι F ≫ Pi.π _ (n + 1) ≫ F.map (homOfLE (n.le_add_right 1)).op =
      homotopyLimitι F ≫ Pi.π _ n := by
  have h := homotopyLimitι_comp_sub_piTowerShift F =≫ Pi.π _ n
  rw [Preadditive.comp_sub, Preadditive.sub_comp, zero_comp, sub_eq_zero, Category.comp_id,
    Category.assoc, piTowerShift_π] at h
  exact h.symm

/-- A chosen homotopy limit cone `R lim F` of a tower `F` with a product `∏ₙ Fₙ`: its legs are
the components of a map `R lim F ⟶ ∏ₙ Fₙ` completing `1 - t` to a distinguished triangle. -/
noncomputable def homotopyLimitCone : Cone F where
  pt := homotopyLimit F
  π := NatTrans.ofOpSequence (fun n ↦ homotopyLimitι F ≫ Pi.π _ n) fun n ↦ by
    simpa using (homotopyLimitι_π_succ F n).symm

@[simp]
lemma homotopyLimitCone_π_app (n : ℕ) :
    (homotopyLimitCone F).π.app (op n) = homotopyLimitι F ≫ Pi.π _ n :=
  rfl

lemma isHomotopyLimit_homotopyLimitCone : IsHomotopyLimit (homotopyLimitCone F) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_homotopyLimitι F
  refine ⟨_, productIsProduct _, δ, ?_⟩
  have hι : Fan.IsLimit.lift (productIsProduct fun n : ℕ ↦ F.obj (op n))
      (fun n ↦ (homotopyLimitCone F).π.app (op n)) = homotopyLimitι F :=
    Pi.hom_ext _ _ fun n ↦ (Fan.IsLimit.fac _ _ n).trans rfl
  rw [hι]
  exact hT


/-- The connecting map `∏ₙ Fₙ ⟶ (R lim F)⟦1⟧` of the chosen Milnor triangle. -/
noncomputable def homotopyLimitδ :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ (homotopyLimit F)⟦(1 : ℤ)⟧ :=
  (exists_distTriang_homotopyLimitι F).choose

/-- The chosen Milnor triangle `R lim F ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ (R lim F)⟦1⟧`. -/
noncomputable abbrev homotopyLimitTriangle : Triangle C :=
  Triangle.mk (homotopyLimitι F) (𝟙 _ - piTowerShift F) (homotopyLimitδ F)

lemma homotopyLimitTriangle_distinguished : homotopyLimitTriangle F ∈ distTriang C :=
  (exists_distTriang_homotopyLimitι F).choose_spec

/-- A cone `s` over a tower lifts to the chosen homotopy limit: there is a map
`s.pt ⟶ R lim F` compatible with the legs. -/
lemma exists_lift_homotopyLimitCone (s : Cone F) :
    ∃ φ : s.pt ⟶ homotopyLimit F, ∀ n : ℕ,
      φ ≫ (homotopyLimitCone F).π.app (op n) = s.π.app (op n) := by
  have hf : (Pi.lift fun n ↦ s.π.app (op n)) ≫ (𝟙 _ - piTowerShift F) = 0 :=
    Pi.hom_ext _ _ fun n ↦ by
      have h := s.w (homOfLE (n.le_add_right 1)).op
      rw [zero_comp, Category.assoc, Preadditive.sub_comp, Category.id_comp, piTowerShift_π,
        Preadditive.comp_sub, Pi.lift_comp_π, Pi.lift_comp_π_assoc, h, sub_self]
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ _ (homotopyLimitTriangle_distinguished F) _ hf
  have hφ' : φ ≫ homotopyLimitι F = Pi.lift fun n ↦ s.π.app (op n) := hφ.symm
  exact ⟨φ, fun n ↦ by rw [homotopyLimitCone_π_app, ← Category.assoc, hφ', Pi.lift_comp_π]⟩

/-- A (non-canonical) lift `s.pt ⟶ R lim F` of a cone over a tower into the chosen homotopy
limit, compatible with the legs (`homotopyLimitLift_π`). -/
noncomputable def homotopyLimitLift (s : Cone F) : s.pt ⟶ homotopyLimit F :=
  (exists_lift_homotopyLimitCone F s).choose

@[reassoc (attr := simp)]
lemma homotopyLimitLift_π (s : Cone F) (n : ℕ) :
    homotopyLimitLift F s ≫ (homotopyLimitCone F).π.app (op n) = s.π.app (op n) :=
  (exists_lift_homotopyLimitCone F s).choose_spec n

end Existence

section Map

variable {F G : ℕᵒᵖ ⥤ C} [HasProduct fun n : ℕ ↦ F.obj (op n)]
  [HasProduct fun n : ℕ ↦ G.obj (op n)] (a : F ⟶ G)

/-- The map `∏ₙ Fₙ ⟶ ∏ₙ Gₙ` induced by a morphism of towers. -/
noncomputable abbrev piTowerMap :
    (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n) :=
  Limits.Pi.map fun n ↦ a.app (op n)

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
lemma piTowerMap_comp_sub_piTowerShift :
    (𝟙 _ - piTowerShift F) ≫ piTowerMap a = piTowerMap a ≫ (𝟙 _ - piTowerShift G) :=
  Pi.hom_ext _ _ fun n ↦ by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
      Category.assoc, piTowerShift_π, Limits.Pi.map_π, Limits.Pi.map_π_assoc]
    rw [← a.naturality, ← piTowerShift_π_assoc]

lemma exists_homotopyLimitTriangle_hom :
    ∃ u : homotopyLimit F ⟶ homotopyLimit G,
      homotopyLimitι F ≫ piTowerMap a = u ≫ homotopyLimitι G ∧
        homotopyLimitδ F ≫ u⟦(1 : ℤ)⟧' = piTowerMap a ≫ homotopyLimitδ G :=
  complete_distinguished_triangle_morphism₁ _ _ (homotopyLimitTriangle_distinguished F)
    (homotopyLimitTriangle_distinguished G) (piTowerMap a) (piTowerMap a)
    (piTowerMap_comp_sub_piTowerShift a)

/-- A map `R lim F ⟶ R lim G` between the chosen homotopy limits induced by a morphism of
towers `a : F ⟶ G`: the first component of a morphism of Milnor triangles extending the map
`∏ a : ∏ₙ Fₙ ⟶ ∏ₙ Gₙ`. It is a choice, unique only up to phantom maps; it is compatible with
the legs (`homotopyLimitMap_π`) and an isomorphism if `a` is (`isIso_homotopyLimitMap`). -/
noncomputable def homotopyLimitMap : homotopyLimit F ⟶ homotopyLimit G :=
  (exists_homotopyLimitTriangle_hom a).choose

/-- The morphism of chosen Milnor triangles induced by a morphism of towers. -/
noncomputable def homotopyLimitTriangleHom : homotopyLimitTriangle F ⟶ homotopyLimitTriangle G :=
  Triangle.homMk _ _ (homotopyLimitMap a) (piTowerMap a) (piTowerMap a)
    (exists_homotopyLimitTriangle_hom a).choose_spec.1 (piTowerMap_comp_sub_piTowerShift a)
    (exists_homotopyLimitTriangle_hom a).choose_spec.2

@[reassoc (attr := simp)]
lemma homotopyLimitMap_π (n : ℕ) :
    homotopyLimitMap a ≫ (homotopyLimitCone G).π.app (op n) =
      (homotopyLimitCone F).π.app (op n) ≫ a.app (op n) := by
  have h := (exists_homotopyLimitTriangle_hom a).choose_spec.1 =≫ Pi.π _ n
  simp only [Category.assoc, Limits.Pi.map_π] at h
  simp only [homotopyLimitCone_π_app, Category.assoc]
  exact h.symm.trans rfl

/-- The map of chosen homotopy limits induced by an isomorphism of towers is an isomorphism. -/
lemma isIso_homotopyLimitMap [∀ n : ℕ, IsIso (a.app (op n))] : IsIso (homotopyLimitMap a) :=
  have : IsIso (piTowerMap a) := ⟨Limits.Pi.map fun n ↦ inv (a.app (op n)),
    Pi.hom_ext _ _ fun n ↦ by simp, Pi.hom_ext _ _ fun n ↦ by simp⟩
  isIso₁_of_isIso₂₃ (homotopyLimitTriangleHom a) (homotopyLimitTriangle_distinguished F)
    (homotopyLimitTriangle_distinguished G) this this


end Map

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Blueprint `lem-cbc-exact-functor-rlim`: Exact functors commute with derived limits of
towers.

Let `Φ : C ⥤ D` be a triangulated functor which commutes with the countable product `∏ₙ Mₙ` of
a tower `M`. If `c` is a homotopy limit cone `R lim M` and `c'` a homotopy limit cone
`R lim Φ(M)`, then there is an isomorphism `Φ(R lim M) ≅ R lim Φ(M)` compatible with the maps to
the terms of the towers: it is the comparison of the two homotopy limit cones `Φ(c)`
(`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`) and `c'` over `M ⋙ Φ`. -/
lemma IsHomotopyLimit.exists_iso_map {M : ℕᵒᵖ ⥤ C} {c : Cone M} (hc : IsHomotopyLimit c)
    (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    [PreservesLimit (Discrete.functor fun n : ℕ ↦ M.obj (op n)) Φ]
    {c' : Cone (M ⋙ Φ)} (hc' : IsHomotopyLimit c') :
    ∃ e : Φ.obj c.pt ≅ c'.pt, ∀ n : ℕ, e.hom ≫ c'.π.app (op n) = Φ.map (c.π.app (op n)) :=
  (hc.map Φ).exists_iso hc'

end CategoryTheory.Pretriangulated
