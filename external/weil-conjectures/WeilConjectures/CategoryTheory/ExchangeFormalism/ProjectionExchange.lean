/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.PushforwardBaseChange
public import WeilConjectures.PoincareDuality.ProjectionCoherence

/-!
# The exchange map and the projection formulas in an exchange formalism

Let `F` be an exchange formalism whose categories are monoidal and whose pullbacks are monoidal,
compatibly with the composition isomorphisms. For a commutative square `t ≫ r = l ≫ b` with `l`
and `r` open immersions whose base change map is an isomorphism,
```
U' --t--> U
|l        |r
Z' --b--> Z
```
the exchange map `r_! t_* ⟶ b_* l_!` intertwines the projection formulas: the projection morphism
of `t^* ⊣ t_*` read through the projection formula of `r_!` and the projection morphism of
`b^* ⊣ b_*` read through the projection formula of `l_!`
(`CategoryTheory.ExchangeFormalism.exchange_whiskerRight_comp_projectionMorphism`; SGA 4,
Exposé XVII, 5.2.2).

-/

@[expose] public section

universe w v₁ v u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] [MonoidalCategory C] {D : Type*} [Category D]
  [MonoidalCategory D] {P : C ⥤ D} {S : D ⥤ C} (adj : P ⊣ S) [S.LaxMonoidal]

/-- The projection comparison transposed along `P ⊣ S`. -/
@[reassoc]
lemma unit_comp_map_projectionComparison (M : C) (N : D) :
    adj.unit.app (M ⊗ S.obj N) ≫ S.map (adj.projectionComparison M N) =
      adj.unit.app M ▷ S.obj N ≫ Functor.LaxMonoidal.μ S (P.obj M) N := by
  exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

end CategoryTheory.Adjunction

namespace CategoryTheory.ExchangeFormalism

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪) [∀ X, MonoidalCategory (F.obj X)]
  [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal]

variable {U' U Z' Z : 𝒞}

/-- The flexible composition isomorphisms of the pullbacks are compatible with the oplax
structures, if the composition isomorphisms are. -/
@[reassoc]
lemma pbComp'_hom_app_tensor
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) (M N : F.obj Z) :
    δ (F.pb h) M N ≫ ((F.pbComp' f g h w).hom.app M ⊗ₘ (F.pbComp' f g h w).hom.app N) =
      (F.pbComp' f g h w).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
        δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N) := by
  subst w
  rw [pbComp'_rfl]
  exact hδ f g M N

/-- The square isomorphism `r^* ⋙ t^* ≅ b^* ⋙ l^*` is compatible with the oplax structures, if
the composition isomorphisms of the pullbacks are. -/
@[reassoc]
lemma sqIso_hom_app_tensor
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) (w : t ≫ r = l ≫ b)
    (M N : F.obj Z) :
    (F.sqIso t l r b w).hom.app (M ⊗ N) ≫ (F.pb l).map (δ (F.pb b) M N) ≫
        δ (F.pb l) ((F.pb b).obj M) ((F.pb b).obj N) =
      (F.pb t).map (δ (F.pb r) M N) ≫ δ (F.pb t) ((F.pb r).obj M) ((F.pb r).obj N) ≫
        ((F.sqIso t l r b w).hom.app M ⊗ₘ (F.sqIso t l r b w).hom.app N) := by
  simp only [sqIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [← pbComp'_hom_app_tensor F hδ l b _ w.symm, ← tensorHom_comp_tensorHom,
    ← cancel_epi ((F.pbComp' t r (t ≫ r) rfl).hom.app (M ⊗ N)), Iso.hom_inv_id_app_assoc,
    ← pbComp'_hom_app_tensor_assoc F hδ t r _ rfl, tensorHom_comp_tensorHom_assoc]
  simp

omit [∀ X, MonoidalCategory (F.obj X)] [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal] in
/-- The base change map transposed along `l_! ⊣ l^*`: it is the unit of `r_! ⊣ r^*` followed by
the square isomorphism. -/
@[reassoc]
lemma unit_comp_map_baseChange (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) (Y : F.obj U) :
    (F.shAdj l).unit.app ((F.pb t).obj Y) ≫
        (F.pb l).map ((F.baseChange t l r b w).app Y) =
      (F.pb t).map ((F.shAdj r).unit.app Y) ≫ (F.sqIso t l r b w).hom.app ((F.sh r).obj Y) := by
  exact (unit_mateEquiv_symm (F.shAdj r) (F.shAdj l) (F.sqIso t l r b w).hom Y).symm

/-- **The base change map is compatible with the projection comparisons**: for a commutative
square `t ≫ r = l ≫ b` with `l`, `r` open immersions, the base change map
`l_! t^* ⟶ b^* r_!` intertwines the projection comparisons of `r_!` and `l_!`, read through the
oplax structures of the pullbacks and the square isomorphism. -/
@[reassoc]
lemma baseChange_app_tensor_comp_projectionComparison
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w : t ≫ r = l ≫ b) (X : F.obj U) (N : F.obj Z) :
    (F.baseChange t l r b w).app (X ⊗ (F.pb r).obj N) ≫
        (F.pb b).map ((F.shAdj r).projectionComparison X N) ≫
        δ (F.pb b) ((F.sh r).obj X) N =
      (F.sh l).map (δ (F.pb t) X ((F.pb r).obj N) ≫
          (F.pb t).obj X ◁ (F.sqIso t l r b w).hom.app N) ≫
        (F.shAdj l).projectionComparison ((F.pb t).obj X) ((F.pb b).obj N) ≫
        (F.baseChange t l r b w).app X ▷ (F.pb b).obj N := by
  apply ((F.shAdj l).homEquiv _ _).injective
  rw [← cancel_mono (δ (F.pb l) ((F.pb b).obj ((F.sh r).obj X)) ((F.pb b).obj N))]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [unit_comp_map_baseChange_assoc, ← Functor.comp_map (F.pb b) (F.pb l),
    ← NatTrans.naturality_assoc, Functor.comp_map, ← Functor.map_comp_assoc,
    Adjunction.unit_comp_map_projectionComparison, sqIso_hom_app_tensor F hδ, Functor.map_comp,
    Category.assoc, ← Functor.map_comp_assoc (F.pb t) (Functor.LaxMonoidal.μ (F.pb r) _ _),
    Functor.Monoidal.μ_δ, Functor.map_id, Category.id_comp]
  simp only [Functor.comp_obj, Adjunction.unit_naturality_assoc,
    Adjunction.unit_comp_map_projectionComparison_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.μ_δ, Category.comp_id,
    ← comp_whiskerRight,
    unit_comp_map_baseChange]
  rw [tensorHom_def', comp_whiskerRight, whisker_exchange_assoc]
  exact (δ_natural_left_assoc (F.pb t) ((F.shAdj r).unit.app X) _ _).symm

/-- The inverse form of
`ExchangeFormalism.baseChange_app_tensor_comp_projectionComparison`, for a square whose base
change map and projection comparisons are isomorphisms. -/
@[reassoc]
lemma inv_projectionComparison_comp_inv_baseChange_app_tensor
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w)]
    [∀ K N, IsIso ((F.shAdj l).projectionComparison K N)]
    [∀ K N, IsIso ((F.shAdj r).projectionComparison K N)] (X : F.obj U) (N : F.obj Z) :
    (F.pb b).map (inv ((F.shAdj r).projectionComparison X N)) ≫
        inv ((F.baseChange t l r b w).app (X ⊗ (F.pb r).obj N)) ≫
        (F.sh l).map (δ (F.pb t) X ((F.pb r).obj N)) =
      δ (F.pb b) ((F.sh r).obj X) N ≫
        inv ((F.baseChange t l r b w).app X) ▷ (F.pb b).obj N ≫
        inv ((F.shAdj l).projectionComparison ((F.pb t).obj X) ((F.pb b).obj N)) ≫
        (F.sh l).map ((F.pb t).obj X ◁ (F.sqIso t l r b w).inv.app N) := by
  rw [← cancel_epi ((F.baseChange t l r b w).app (X ⊗ (F.pb r).obj N) ≫
    (F.pb b).map ((F.shAdj r).projectionComparison X N))]
  simp only [Category.assoc]
  rw [baseChange_app_tensor_comp_projectionComparison_assoc F hδ]
  simp

omit [∀ X, MonoidalCategory (F.obj X)] [∀ {X Y : 𝒞} (f : X ⟶ Y), (F.pb f).Monoidal] in
/-- The naturality of the inverse of the base change map. -/
@[reassoc]
lemma map_map_comp_inv_baseChange_app (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] (w : t ≫ r = l ≫ b)
    [IsIso (F.baseChange t l r b w)] {Y Y' : F.obj U} (f : Y ⟶ Y') :
    (F.pb b).map ((F.sh r).map f) ≫ inv ((F.baseChange t l r b w).app Y') =
      inv ((F.baseChange t l r b w).app Y) ≫ (F.sh l).map ((F.pb t).map f) := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact ((F.baseChange t l r b w).naturality f).symm

/-- **The exchange map intertwines the projection formulas**: for a commutative square
`t ≫ r = l ≫ b` with `l`, `r` open immersions whose base change map is an isomorphism, the
square
```
r_! t_* A ⊗ N ──ex ▷ N──▶ b_* l_! A ⊗ N ──PF_b──▶ b_* (l_! A ⊗ b^* N)
      │ q_r⁻¹                                          │ b_* q_l⁻¹
      ▼                                                ▼
r_! (t_* A ⊗ r^* N)                         b_* l_! (A ⊗ l^* b^* N)
      │ r_! PF_t                                       │ ≅
      ▼                                                ▼
r_! t_* (A ⊗ t^* r^* N) ──────────ex──────────▶ b_* l_! (A ⊗ t^* r^* N)
```
commutes, where `ex` is the exchange map, `PF` the projection morphisms of the
pullback–pushforward adjunctions, `q` the projection comparisons of the extensions by zero
and `l^* b^* ≅ t^* r^*` the square isomorphism. -/
theorem exchange_whiskerRight_comp_projectionMorphism
    (hδ : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) (M N : F.obj Z),
      δ (F.pb (f ≫ g)) M N ≫ ((F.pbComp f g).hom.app M ⊗ₘ (F.pbComp f g).hom.app N) =
        (F.pbComp f g).hom.app (M ⊗ N) ≫ (F.pb f).map (δ (F.pb g) M N) ≫
          δ (F.pb f) ((F.pb g).obj M) ((F.pb g).obj N))
    (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z) [Fact (𝒪 l)] [Fact (𝒪 r)]
    (w : t ≫ r = l ≫ b) [IsIso (F.baseChange t l r b w)]
    [∀ K N, IsIso ((F.shAdj l).projectionComparison K N)]
    [∀ K N, IsIso ((F.shAdj r).projectionComparison K N)] (A : F.obj U') (N : F.obj Z) :
    (F.exchange t l r b w).app A ▷ N ≫
        (F.adj b).projectionMorphism ((F.sh l).obj A) N ≫
        (F.pf b).map (inv ((F.shAdj l).projectionComparison A ((F.pb b).obj N)) ≫
          (F.sh l).map (A ◁ (F.sqIso t l r b w).inv.app N)) =
      inv ((F.shAdj r).projectionComparison ((F.pf t).obj A) N) ≫
        (F.sh r).map ((F.adj t).projectionMorphism A ((F.pb r).obj N)) ≫
        (F.exchange t l r b w).app (A ⊗ (F.pb t).obj ((F.pb r).obj N)) := by
  apply ((F.adj b).homEquiv _ _).symm.injective
  simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    exchange_counit, map_map_comp_inv_baseChange_app_assoc]
  rw [← Functor.map_comp (F.sh l), Adjunction.projectionMorphism, Adjunction.projectionMorphism,
    Adjunction.map_homEquiv_comp_counit, reassoc_of% Adjunction.map_homEquiv_comp_counit,
    Category.assoc]
  erw [← δ_natural_left_assoc]
  rw [← comp_whiskerRight_assoc, exchange_counit, Functor.map_comp,
    inv_projectionComparison_comp_inv_baseChange_app_tensor_assoc F hδ, comp_whiskerRight_assoc]
  erw [Adjunction.inv_projectionComparison_natural_left_assoc]
  rw [← Functor.map_comp (F.sh l), ← Functor.map_comp (F.sh l), whisker_exchange]
  rfl

end CategoryTheory.ExchangeFormalism
