/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal

/-!
# Projection maps and cup products of a composite pushforward

Let `C`, `D`, `E` be monoidal categories, `adj : F ⊣ G` an adjunction with `F : D ⥤ E` and a
comparison `φ : F (a ⊗ b) ⟶ F a ⊗ F b`, and `J : C ⥤ E` a functor with a *mixed projection map*
`ψ K N : J K ⊗ N ⟶ J (K ⊗ F' N)` for a functor `F' : E ⥤ C`. Given `e L : F' (F L) ⟶ F'' L` for a
functor `F'' : D ⥤ C`, the composite `G ∘ J : C ⥤ D` has the projection map
```
pm K L : G (J K) ⊗ L ⟶ G (J K ⊗ F L) ⟶ G (J (K ⊗ F' (F L))) ⟶ G (J (K ⊗ F'' L))
```
(`CategoryTheory.Adjunction.compProjectionMap`), the composite of the projection map of `G`, of
`G ψ` and of `G (J (K ◁ e L))`. This is the shape of the projection map
`Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of a compactly supported direct image `Rf_! = Rg_* ∘ j_!`.

If moreover `adj'' : F'' ⊣ G''`, the *mixed cup product*
```
cup K L : G (J K) ⊗ G'' L ⟶ G (J (K ⊗ F'' (G'' L))) ⟶ G (J (K ⊗ L))
```
is `pm` followed by the counit of `F'' ⊣ G''`, that is,
`CategoryTheory.Adjunction.cupProductOfProjection` applied to
`CategoryTheory.Adjunction.compProjectionMap`.

We show that `pm` and the cup product are natural, associative and unital, and compatible with a
map `J ⟶ G'` to a right adjoint of `F'` (the forget-supports map `j_! ⟶ Rj_*`), provided the
ingredients satisfy the corresponding axioms. The axioms are stated as hypotheses, so that the
results apply to the six operations on derived categories of étale sheaves.

## Main definitions

- `CategoryTheory.Adjunction.compProjectionMap`: the projection map `Π` of `G ∘ J`.
- `CategoryTheory.Adjunction.rightAdjointCupProduct`: the cup product
  `G'' M ⊗ G'' L ⟶ G'' (M ⊗ L)` of a right adjoint, `π` followed by the counit.
- `CategoryTheory.Adjunction.cupProductOfProjection`: the cup product `P K ⊗ G M ⟶ P (K ⊗ M)`
  attached to a projection map of `P`; applied to `compProjectionMap` it is the mixed cup product.

## Main statements

- `CategoryTheory.Adjunction.compProjectionMap_associativity`,
  `CategoryTheory.Adjunction.compProjectionMap_rightUnitality`,
  `CategoryTheory.Adjunction.compProjectionMap_comp`: coherence of `pm`.
- `CategoryTheory.Adjunction.cupProductOfProjection_associativity`,
  `CategoryTheory.Adjunction.cupProductOfProjection_rightUnitality`,
  `CategoryTheory.Adjunction.cupProductOfProjection_comp`: coherence of the cup product attached
  to a projection map, in particular of the mixed cup product.
- `CategoryTheory.Adjunction.rightAdjointCupProduct_associativity`: associativity of the cup
  product of a right adjoint.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open MonoidalCategory _root_.CategoryTheory.Functor

section RightAdjointCupProduct

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- The cup product `G M ⊗ G L ⟶ G (M ⊗ L)` of a right adjoint `G`: the projection map
`G M ⊗ G L ⟶ G (M ⊗ F (G L))` followed by `G (M ◁ ε_L)` for the counit `ε` of `F ⊣ G`. -/
noncomputable def rightAdjointCupProduct (M L : C) : G.obj M ⊗ G.obj L ⟶ G.obj (M ⊗ L) :=
  ((adj.rightAdjointProjectionMap φ).app M).app (G.obj L) ≫ G.map (M ◁ adj.counit.app L)

/-- The transpose of the cup product of a right adjoint is `φ` followed by `ε ⊗ ε`. -/
@[reassoc]
lemma map_rightAdjointCupProduct_comp_counit (M L : C) :
    F.map (adj.rightAdjointCupProduct φ M L) ≫ adj.counit.app _ =
      (φ.app (G.obj M)).app (G.obj L) ≫ adj.counit.app M ▷ F.obj (G.obj L) ≫
        M ◁ adj.counit.app L := by
  rw [rightAdjointCupProduct, F.map_comp, Category.assoc]
  erw [adj.counit_naturality]
  rw [map_rightAdjointProjectionMap_app_app_comp_counit_assoc, curriedTensor_map_app]

/-- The right adjoint projection map is natural in its first variable. -/
@[reassoc]
lemma rightAdjointProjectionMap_naturality_left {M M' : C} (x : M ⟶ M') (L : D) :
    G.map x ▷ L ≫ ((adj.rightAdjointProjectionMap φ).app M').app L =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫ G.map (x ▷ F.obj L) :=
  NatTrans.congr_app ((adj.rightAdjointProjectionMap φ).naturality x) L

/-- The right adjoint projection map is natural in its second variable. -/
@[reassoc]
lemma rightAdjointProjectionMap_naturality_right (M : C) {L L' : D} (y : L ⟶ L') :
    G.obj M ◁ y ≫ ((adj.rightAdjointProjectionMap φ).app M).app L' =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫ G.map (M ◁ F.map y) :=
  ((adj.rightAdjointProjectionMap φ).app M).naturality y

end RightAdjointCupProduct

section CupProduct

/-! ### The cup product attached to a projection map

Let `P : C ⥤ D` be a functor with a projection map `pm K L : P K ⊗ L ⟶ P (K ⊗ F L)` for a left
adjoint `F : D ⥤ C` of `G`. The *cup product* `P K ⊗ G M ⟶ P (K ⊗ M)` is `pm` followed by
`P (K ◁ ε_M)`. Its coherence follows from that of `pm`. -/

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
  (P : C ⥤ D) (pm : ∀ (K : C) (L : D), P.obj K ⊗ L ⟶ P.obj (K ⊗ F.obj L))

/-- The cup product `P K ⊗ G M ⟶ P (K ⊗ M)` attached to a projection map
`pm K L : P K ⊗ L ⟶ P (K ⊗ F L)`: `pm` followed by `P (K ◁ ε_M)`. -/
noncomputable def cupProductOfProjection (K M : C) : P.obj K ⊗ G.obj M ⟶ P.obj (K ⊗ M) :=
  pm K (G.obj M) ≫ P.map (K ◁ adj.counit.app M)

variable {P pm}

/-- The cup product attached to a projection map is natural in its first variable. -/
lemma cupProductOfProjection_naturality_left
    (hpm : ∀ {K K' : C} (x : K ⟶ K') (L : D),
      P.map x ▷ L ≫ pm K' L = pm K L ≫ P.map (x ▷ F.obj L))
    {K K' : C} (x : K ⟶ K') (M : C) :
    P.map x ▷ G.obj M ≫ adj.cupProductOfProjection P pm K' M =
      adj.cupProductOfProjection P pm K M ≫ P.map (x ▷ M) := by
  simp only [cupProductOfProjection, Category.assoc, reassoc_of% (hpm x (G.obj M)),
    ← P.map_comp,
    whisker_exchange]

/-- The cup product attached to a projection map is natural in its second variable. -/
lemma cupProductOfProjection_naturality_right
    (hpm : ∀ (K : C) {L L' : D} (y : L ⟶ L'),
      P.obj K ◁ y ≫ pm K L' = pm K L ≫ P.map (K ◁ F.map y))
    (K : C) {M M' : C} (y : M ⟶ M') :
    P.obj K ◁ G.map y ≫ adj.cupProductOfProjection P pm K M' =
      adj.cupProductOfProjection P pm K M ≫ P.map (K ◁ y) := by
  simp only [cupProductOfProjection, Category.assoc, reassoc_of% (hpm K (G.map y)),
    ← P.map_comp,
    ← MonoidalCategory.whiskerLeft_comp, adj.counit_naturality]

/-- **Associativity of the cup product attached to a projection map**, given the naturality and
associativity of the projection map. Writing `⌣` for `cupProductOfProjection` and `∪` for
`rightAdjointCupProduct`:
```
(P K ⊗ G L) ⊗ G M --⌣ ▷ G M--> P (K ⊗ L) ⊗ G M --⌣--> P ((K ⊗ L) ⊗ M)
        | α                                               | P α
        v                                                 v
P K ⊗ (G L ⊗ G M) --P K ◁ ∪--> P K ⊗ G (L ⊗ M) --⌣--> P (K ⊗ (L ⊗ M))
```
-/
lemma cupProductOfProjection_associativity
    (hpml : ∀ {K K' : C} (x : K ⟶ K') (L : D),
      P.map x ▷ L ≫ pm K' L = pm K L ≫ P.map (x ▷ F.obj L))
    (hpmr : ∀ (K : C) {L L' : D} (y : L ⟶ L'),
      P.obj K ◁ y ≫ pm K L' = pm K L ≫ P.map (K ◁ F.map y))
    (hpm : ∀ (K : C) (L L' : D), pm K L ▷ L' ≫ pm (K ⊗ F.obj L) L' ≫ P.map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ pm K (L ⊗ L') ≫ P.map (K ◁ (φ.app L).app L'))
    (K L M : C) :
    adj.cupProductOfProjection P pm K L ▷ G.obj M ≫
        adj.cupProductOfProjection P pm (K ⊗ L) M ≫ P.map (α_ K L M).hom =
      (α_ _ _ _).hom ≫ P.obj K ◁ adj.rightAdjointCupProduct φ L M ≫
        adj.cupProductOfProjection P pm K (L ⊗ M) := by
  have h₁ : pm K (G.obj L) ▷ G.obj M ≫ pm (K ⊗ F.obj (G.obj L)) (G.obj M) =
      (α_ _ _ _).hom ≫ pm K (G.obj L ⊗ G.obj M) ≫
        P.map (K ◁ (φ.app (G.obj L)).app (G.obj M) ≫ (α_ _ _ _).inv) := by
    rw [← cancel_mono (P.map (α_ _ _ _).hom), Category.assoc, hpm]
    simp only [Category.assoc, ← P.map_comp, Iso.inv_hom_id, Category.comp_id]
  have h₂ := hpmr K (adj.rightAdjointCupProduct φ L M)
  simp only [cupProductOfProjection, comp_whiskerRight, Category.assoc]
  rw [reassoc_of% (hpml (K ◁ adj.counit.app L) (G.obj M)), reassoc_of% h₁, reassoc_of% h₂]
  simp only [← P.map_comp, ← MonoidalCategory.whiskerLeft_comp,
    map_rightAdjointCupProduct_comp_counit]
  congr 3
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- **Unitality of the cup product attached to a projection map**: the unit
`1 : 𝟙_ ⟶ G (𝟙_)`, the transpose of `η : F (𝟙_) ⟶ 𝟙_`, acts as the identity, given the
naturality and unitality of the projection map. -/
lemma cupProductOfProjection_rightUnitality (η : F.obj (𝟙_ D) ⟶ 𝟙_ C)
    (hpmr : ∀ (K : C) {L L' : D} (y : L ⟶ L'),
      P.obj K ◁ y ≫ pm K L' = pm K L ≫ P.map (K ◁ F.map y))
    (hpm : ∀ K : C, pm K (𝟙_ D) ≫ P.map (K ◁ η ≫ (ρ_ K).hom) = (ρ_ _).hom)
    (K : C) :
    P.obj K ◁ adj.homEquiv _ _ η ≫ adj.cupProductOfProjection P pm K (𝟙_ C) ≫
        P.map (ρ_ K).hom =
      (ρ_ _).hom := by
  rw [cupProductOfProjection, Category.assoc, reassoc_of% (hpmr K (adj.homEquiv _ _ η)),
    ← P.map_comp,
    ← P.map_comp, ← MonoidalCategory.whiskerLeft_comp_assoc, ← homEquiv_counit,
    Equiv.symm_apply_apply, hpm]

/-- **Compatibility of the cup product with a map to `G`**: if `s : P ⟶ G` intertwines `pm` with
the projection map of `G`, it intertwines the cup products `⌣` (`cupProductOfProjection`) and
`∪` (`rightAdjointCupProduct`):
```
P K ⊗ G M --⌣--> P (K ⊗ M)
   | s ▷ G M         | s
   v                 v
G K ⊗ G M --∪--> G (K ⊗ M)
```
-/
lemma cupProductOfProjection_comp (s : P ⟶ G)
    (hs : ∀ (K : C) (L : D), pm K L ≫ s.app (K ⊗ F.obj L) =
      s.app K ▷ L ≫ ((adj.rightAdjointProjectionMap φ).app K).app L)
    (K M : C) :
    adj.cupProductOfProjection P pm K M ≫ s.app (K ⊗ M) =
      s.app K ▷ G.obj M ≫ adj.rightAdjointCupProduct φ K M := by
  rw [cupProductOfProjection, Category.assoc, s.naturality, reassoc_of% hs]
  rfl

end CupProduct

section CompProjectionMap

/-! ### The projection map of a composite `G ∘ J` -/

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G)
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ E).obj F).obj F).obj (curriedTensor E))
  (J : C ⥤ E) {F' : E ⥤ C} {F'' : D ⥤ C}
  (ψ : ∀ (K : C) (N : E), J.obj K ⊗ N ⟶ J.obj (K ⊗ F'.obj N))
  (e : ∀ L : D, F'.obj (F.obj L) ⟶ F''.obj L)

/-- The projection map `G (J K) ⊗ L ⟶ G (J (K ⊗ F'' L))` of the composite `G ∘ J`: the projection
map of `G`, followed by `G ψ` and `G (J (K ◁ e L))`. -/
noncomputable def compProjectionMap (K : C) (L : D) :
    (J ⋙ G).obj K ⊗ L ⟶ (J ⋙ G).obj (K ⊗ F''.obj L) :=
  ((adj.rightAdjointProjectionMap φ).app (J.obj K)).app L ≫ G.map (ψ K (F.obj L)) ≫
    G.map (J.map (K ◁ e L))

variable {J ψ e}

/-- The projection map of `G ∘ J` is natural in its first variable. -/
@[reassoc]
lemma compProjectionMap_naturality_left
    (hψ : ∀ {K K' : C} (x : K ⟶ K') (N : E),
      J.map x ▷ N ≫ ψ K' N = ψ K N ≫ J.map (x ▷ F'.obj N))
    {K K' : C} (x : K ⟶ K') (L : D) :
    (J ⋙ G).map x ▷ L ≫ adj.compProjectionMap φ J ψ e K' L =
      adj.compProjectionMap φ J ψ e K L ≫ (J ⋙ G).map (x ▷ F''.obj L) := by
  simp only [compProjectionMap, Functor.comp_map,
    adj.rightAdjointProjectionMap_naturality_left_assoc,
    Category.assoc, ← G.map_comp, ← J.map_comp, whisker_exchange]
  rw [reassoc_of% (hψ x (F.obj L)), ← J.map_comp]

/-- The projection map of `G ∘ J` is natural in its second variable. -/
@[reassoc]
lemma compProjectionMap_naturality_right
    (hψ : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      J.obj K ◁ y ≫ ψ K N' = ψ K N ≫ J.map (K ◁ F'.map y))
    (he : ∀ {L L' : D} (y : L ⟶ L'), F'.map (F.map y) ≫ e L' = e L ≫ F''.map y)
    (K : C) {L L' : D} (y : L ⟶ L') :
    (J ⋙ G).obj K ◁ y ≫ adj.compProjectionMap φ J ψ e K L' =
      adj.compProjectionMap φ J ψ e K L ≫ (J ⋙ G).map (K ◁ F''.map y) := by
  simp only [compProjectionMap, Functor.comp_obj, Functor.comp_map,
    adj.rightAdjointProjectionMap_naturality_right_assoc,
    Category.assoc, ← G.map_comp, ← J.map_comp, ← MonoidalCategory.whiskerLeft_comp]
  rw [reassoc_of% (hψ K (F.map y)), ← J.map_comp, ← MonoidalCategory.whiskerLeft_comp, he]

/-- **Associativity of the projection map of `G ∘ J`**, given the associativity of `φ` and `ψ`
and the compatibility of `e` with the comparisons `φ`, `φ'` and `φ''`. Writing `pm` for
`compProjectionMap` and `GJ` for `J ⋙ G`:
```
(GJ K ⊗ L) ⊗ L' --pm ▷ L'--> GJ (K ⊗ F'' L) ⊗ L' --pm--> GJ ((K ⊗ F'' L) ⊗ F'' L')
      | α                                                     | GJ α
      v                                                       v
GJ K ⊗ (L ⊗ L') --pm--> GJ (K ⊗ F'' (L ⊗ L')) --GJ (K ◁ φ'')--> GJ (K ⊗ (F'' L ⊗ F'' L'))
```
-/
lemma compProjectionMap_associativity
    (φ' : ∀ N N' : E, F'.obj (N ⊗ N') ⟶ F'.obj N ⊗ F'.obj N')
    (φ'' : ∀ L L' : D, F''.obj (L ⊗ L') ⟶ F''.obj L ⊗ F''.obj L')
    (hφ : ∀ X Y Z : D, (φ.app (X ⊗ Y)).app Z ≫ (φ.app X).app Y ▷ F.obj Z ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ (φ.app X).app (Y ⊗ Z) ≫ F.obj X ◁ (φ.app Y).app Z)
    (hψl : ∀ {K K' : C} (x : K ⟶ K') (N : E),
      J.map x ▷ N ≫ ψ K' N = ψ K N ≫ J.map (x ▷ F'.obj N))
    (hψr : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      J.obj K ◁ y ≫ ψ K N' = ψ K N ≫ J.map (K ◁ F'.map y))
    (hψ : ∀ (K : C) (N N' : E), ψ K N ▷ N' ≫ ψ (K ⊗ F'.obj N) N' =
      (α_ _ _ _).hom ≫ ψ K (N ⊗ N') ≫ J.map (K ◁ φ' N N' ≫ (α_ _ _ _).inv))
    (he : ∀ L L' : D, e (L ⊗ L') ≫ φ'' L L' =
      F'.map ((φ.app L).app L') ≫ φ' _ _ ≫ (e L ⊗ₘ e L'))
    (K : C) (L L' : D) :
    adj.compProjectionMap φ J ψ e K L ▷ L' ≫ adj.compProjectionMap φ J ψ e (K ⊗ F''.obj L) L' ≫
        (J ⋙ G).map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ adj.compProjectionMap φ J ψ e K (L ⊗ L') ≫
        (J ⋙ G).map (K ◁ φ'' L L') := by
  have h₁ : ((adj.rightAdjointProjectionMap φ).app (J.obj K)).app L ▷ L' ≫
      ((adj.rightAdjointProjectionMap φ).app (J.obj K ⊗ F.obj L)).app L' =
        (α_ _ _ _).hom ≫ ((adj.rightAdjointProjectionMap φ).app (J.obj K)).app (L ⊗ L') ≫
          G.map (J.obj K ◁ (φ.app L).app L' ≫ (α_ _ _ _).inv) := by
    rw [← cancel_mono (G.map (α_ _ _ _).hom), Category.assoc,
      adj.rightAdjointProjectionMap_associativity φ hφ]
    simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, Category.comp_id]
  simp only [compProjectionMap, comp_whiskerRight, Category.assoc, Functor.comp_map]
  rw [adj.rightAdjointProjectionMap_naturality_left_assoc,
    adj.rightAdjointProjectionMap_naturality_left_assoc]
  erw [reassoc_of% h₁]
  simp only [← G.map_comp]
  congr 3
  simp only [Category.assoc]
  rw [reassoc_of% (hψl (K ◁ e L) (F.obj L')), reassoc_of% (hψ K _ _), Iso.inv_hom_id_assoc]
  erw [reassoc_of% (hψr K ((φ.app L).app L'))]
  simp only [← J.map_comp]
  congr 2
  rw [← MonoidalCategory.whiskerLeft_comp, he, tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- **Unitality of the projection map of `G ∘ J`**, given the unitality of `φ` and `ψ` and the
compatibility of `e` with the unit comparisons. -/
lemma compProjectionMap_rightUnitality (η : F.obj (𝟙_ D) ⟶ 𝟙_ E) (η' : F'.obj (𝟙_ E) ⟶ 𝟙_ C)
    (η'' : F''.obj (𝟙_ D) ⟶ 𝟙_ C)
    (hη : ∀ X : D, (φ.app X).app (𝟙_ D) ≫ F.obj X ◁ η ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom)
    (hψr : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      J.obj K ◁ y ≫ ψ K N' = ψ K N ≫ J.map (K ◁ F'.map y))
    (hψ : ∀ K : C, ψ K (𝟙_ E) ≫ J.map (K ◁ η' ≫ (ρ_ K).hom) = (ρ_ _).hom)
    (he : e (𝟙_ D) ≫ η'' = F'.map η ≫ η')
    (K : C) :
    adj.compProjectionMap φ J ψ e K (𝟙_ D) ≫ (J ⋙ G).map (K ◁ η'' ≫ (ρ_ K).hom) =
      (ρ_ _).hom := by
  simp only [compProjectionMap, Category.assoc, Functor.comp_map, ← G.map_comp, ← J.map_comp,
    ← MonoidalCategory.whiskerLeft_comp_assoc, he]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, J.map_comp, ← reassoc_of% (hψr K η),
    G.map_comp, ← G.map_comp, hψ]
  rw [G.map_comp]
  exact adj.rightAdjointProjectionMap_rightUnitality φ η hη (J.obj K)

/-- **Compatibility of the projection map of `G ∘ J` with a map to a right adjoint.** Let
`s : J ⟶ G'` for a right adjoint `G'` of `F'`, compatible with the projection maps
(hypothesis `hs`), and let `κ : G' ⋙ G ⟶ G''` for a right adjoint `G''` of `F''`, compatible with
the projection maps (hypothesis `hκ`, the projection map of a composite). Then, writing `pm` for
`compProjectionMap`, `π''` for the projection map of `G''` and `t` for `G s ≫ κ : J ⋙ G ⟶ G''`:
```
G (J K) ⊗ L --pm--> G (J (K ⊗ F'' L))
    | t ▷ L              | t
    v                    v
 G'' K ⊗ L  --π''--> G'' (K ⊗ F'' L)
```
-/
lemma compProjectionMap_comp {G' : C ⥤ E} {G'' : C ⥤ D} (adj' : F' ⊣ G') (adj'' : F'' ⊣ G'')
    (φ' : (postcompose₂.obj F').obj (curriedTensor E) ⟶
      (((whiskeringLeft₂ C).obj F').obj F').obj (curriedTensor C))
    (φ'' : (postcompose₂.obj F'').obj (curriedTensor D) ⟶
      (((whiskeringLeft₂ C).obj F'').obj F'').obj (curriedTensor C))
    (s : J ⟶ G') (κ : G' ⋙ G ⟶ G'')
    (hs : ∀ (K : C) (N : E), ψ K N ≫ s.app (K ⊗ F'.obj N) =
      s.app K ▷ N ≫ ((adj'.rightAdjointProjectionMap φ').app K).app N)
    (hκ : ∀ (M : C) (L : D), κ.app M ▷ L ≫ ((adj''.rightAdjointProjectionMap φ'').app M).app L =
      ((adj.rightAdjointProjectionMap φ).app (G'.obj M)).app L ≫
        G.map (((adj'.rightAdjointProjectionMap φ').app M).app (F.obj L)) ≫
        κ.app (M ⊗ F'.obj (F.obj L)) ≫ G''.map (M ◁ e L))
    (K : C) (L : D) :
    adj.compProjectionMap φ J ψ e K L ≫ (Functor.whiskerRight s G ≫ κ).app (K ⊗ F''.obj L) =
      (Functor.whiskerRight s G ≫ κ).app K ▷ L ≫
        ((adj''.rightAdjointProjectionMap φ'').app K).app L := by
  simp only [compProjectionMap, NatTrans.comp_app, Functor.whiskerRight_app, comp_whiskerRight,
    Category.assoc, hκ]
  rw [adj.rightAdjointProjectionMap_naturality_left_assoc]
  congr 1
  simp only [← G.map_comp_assoc, s.naturality, reassoc_of% (hs K (F.obj L))]
  simp only [G.map_comp, Category.assoc]
  erw [κ.naturality]

end CompProjectionMap

section RightAdjointCupProduct

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  (φ : (postcompose₂.obj F).obj (curriedTensor D) ⟶
    (((whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))

/-- **Associativity of the cup product of a right adjoint**, if `φ` satisfies the associativity
axiom of an oplax monoidal functor. -/
lemma rightAdjointCupProduct_associativity
    (hφ : ∀ X Y Z : D, (φ.app (X ⊗ Y)).app Z ≫ (φ.app X).app Y ▷ F.obj Z ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ (φ.app X).app (Y ⊗ Z) ≫ F.obj X ◁ (φ.app Y).app Z)
    (K L M : C) :
    adj.rightAdjointCupProduct φ K L ▷ G.obj M ≫ adj.rightAdjointCupProduct φ (K ⊗ L) M ≫
        G.map (α_ K L M).hom =
      (α_ _ _ _).hom ≫ G.obj K ◁ adj.rightAdjointCupProduct φ L M ≫
        adj.rightAdjointCupProduct φ K (L ⊗ M) :=
  adj.cupProductOfProjection_associativity φ
    (fun x L ↦ adj.rightAdjointProjectionMap_naturality_left φ x L)
    (fun K _ _ y ↦ adj.rightAdjointProjectionMap_naturality_right φ K y)
    (fun K L L' ↦ adj.rightAdjointProjectionMap_associativity φ hφ K L L') K L M

end RightAdjointCupProduct

end CategoryTheory.Adjunction
