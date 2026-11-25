/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# The projection map of an adjunction

Let `adj : F ⊣ G` be an adjunction with `F : C ⥤ D`, let `T : C ⥤ C ⥤ C` and
`T' : D ⥤ D ⥤ D` be bifunctors (typically tensor products, written `⊗` below), let
`G' : D ⥤ C` be a functor and let `δ : G X ⊗ G' Y ⟶ G (X ⊗ Y)` be natural in `X` and `Y`.
The *projection map* is the morphism of bifunctors
```
F (K ⊗ G' M) ⟶ F K ⊗ M
```
whose transpose along `F ⊣ G` is
```
K ⊗ G' M --(η ⊗ 1)--> G (F K) ⊗ G' M --δ--> G (F K ⊗ M).
```
The typical example is a right adjoint `G = G'` with a strong monoidal structure and `δ` the
inverse of its comparison; then the projection map is an isomorphism for example when `F`
is the extension by zero along an open immersion.

## The right adjoint form

Dually, let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, let `T_C : C ⥤ C ⥤ C` and
`T_D : D ⥤ D ⥤ D` be bifunctors, and let `φ : F (T_D a b) ⟶ T_C (F a) (F b)` be a natural
transformation of bifunctors `D ⥤ D ⥤ C`. The *right adjoint projection map* is the morphism
of bifunctors `T_D (G M) L ⟶ G (T_C M (F L))`, natural in `M` in `C` and `L` in `D`, whose
transpose along `adj` is the composite
```
F (T_D (G M) L) --φ--> T_C (F (G M)) (F L) --T_C (ε_M) (𝟙 (F L))--> T_C M (F L)
```
where `ε` is the counit of `adj`. When `T_C` and `T_D` are tensor products and `φ` is the
oplax monoidal structure of `F`, this is the classical projection map
`G M ⊗ L ⟶ G (M ⊗ F L)`, used for example for derived pushforwards.

## Main definitions and results

- `CategoryTheory.Adjunction.projectionMapTranspose`: the morphism
  `K ⊗ G' M ⟶ G (F K ⊗ M)` above. It is an isomorphism if the unit of `adj` and `δ` are.
- `CategoryTheory.Adjunction.projectionMap`: its transpose `F (K ⊗ G' M) ⟶ F K ⊗ M`.
- `CategoryTheory.Adjunction.isIso_map_projectionMap_app_app`: `G` of the projection map is
  an isomorphism if the unit of `adj` and `δ` are.
- `CategoryTheory.Adjunction.rightAdjointProjectionMap adj φ`: the right adjoint projection map
  `T_D (G M) L ⟶ G (T_C M (F L))`, as a natural transformation of bifunctors `C ⥤ D ⥤ D`.
- `CategoryTheory.Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app`: its transpose
  along `adj` is `φ` followed by the counit of `adj` in the first variable.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

section LeftAdjoint

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  (G' : D ⥤ C) (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
  (δ : (((Functor.whiskeringLeft₂ C).obj G).obj G').obj T ⟶
    (Functor.postcompose₂.obj G).obj T')

/-- The morphism `K ⊗ G' M ⟶ G (F K ⊗ M)` of bifunctors `C ⥤ D ⥤ C`, the composite
```
K ⊗ G' M --(η ⊗ 1)--> G (F K) ⊗ G' M --δ--> G (F K ⊗ M)
```
where `η` is the unit of `adj`. Its transpose is `Adjunction.projectionMap`. -/
noncomputable def projectionMapTranspose :
    (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj G').obj T ⟶
      (Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj T') :=
  (((Functor.whiskeringLeft₂ C).map adj.unit).app G').app T ≫
    (((Functor.whiskeringLeft₂ C).obj F).obj (𝟭 D)).map δ

instance isIso_projectionMapTranspose [IsIso adj.unit] [IsIso δ] :
    IsIso (adj.projectionMapTranspose G' T T' δ) := by
  dsimp only [projectionMapTranspose]
  infer_instance

/-- The **projection map** `F (K ⊗ G' M) ⟶ F K ⊗ M` of bifunctors `C ⥤ D ⥤ D`: the transpose
along `F ⊣ G` of `Adjunction.projectionMapTranspose`, that is the composite
```
F (K ⊗ G' M) --F(φ)--> F (G (F K ⊗ M)) --ε--> F K ⊗ M
```
where `φ = (η ⊗ 1) ≫ δ` is `Adjunction.projectionMapTranspose` and `ε` is the counit of
`adj`. -/
noncomputable def projectionMap :
    (Functor.postcompose₂.obj F).obj ((((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj G').obj T) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj T' :=
  (Functor.postcompose₂.obj F).map (adj.projectionMapTranspose G' T T' δ) ≫
    (Functor.postcompose₂.map adj.counit).app _

/-- The components of the projection map are the transposes along `F ⊣ G` of the components
`φ` of `Adjunction.projectionMapTranspose`:
```
F (K ⊗ G' M) --F(φ)--> F (G (F K ⊗ M))
        \                    |
         \                   | ε
       projection            v
           ----------->  F K ⊗ M
```
-/
lemma projectionMap_app_app (K : C) (M : D) :
    ((adj.projectionMap G' T T' δ).app K).app M =
      (adj.homEquiv _ _).symm (((adj.projectionMapTranspose G' T T' δ).app K).app M) := by
  simp [projectionMap, homEquiv_counit]

/-- `G` of the projection map, preceded by the unit, is `Adjunction.projectionMapTranspose`:
```
K ⊗ G' M ---------η---------> G (F (K ⊗ G' M))
        \                             |
         \                            | G(projection)
          φ                           v
           ------------------>  G (F K ⊗ M)
```
-/
@[reassoc]
lemma unit_app_comp_map_projectionMap_app_app (K : C) (M : D) :
    adj.unit.app _ ≫ G.map (((adj.projectionMap G' T T' δ).app K).app M) =
      ((adj.projectionMapTranspose G' T T' δ).app K).app M := by
  refine (adj.homEquiv_unit _ _ _).symm.trans ?_
  rw [projectionMap_app_app]
  exact Equiv.apply_symm_apply _ _

/-- `G` of the projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` is an isomorphism if the unit of
`F ⊣ G` and `δ` are. -/
lemma isIso_map_projectionMap_app_app [IsIso adj.unit] [IsIso δ] (K : C) (M : D) :
    IsIso (G.map (((adj.projectionMap G' T T' δ).app K).app M)) := by
  rw [(IsIso.eq_inv_comp _).2 (adj.unit_app_comp_map_projectionMap_app_app G' T T' δ K M)]
  infer_instance

/-- The projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` is an isomorphism if the unit of `F ⊣ G` and
`δ` are isomorphisms and its target `F K ⊗ M` lies in the essential image of `F`: it is then
`F` of the isomorphism `Adjunction.projectionMapTranspose` followed by the counit at an object
of the essential image of the fully faithful `F`. -/
lemma isIso_projectionMap_app_app_of_iso [IsIso adj.unit] [IsIso δ] (K : C) (M : D) (Z : C)
    (e : (T'.obj (F.obj K)).obj M ≅ F.obj Z) :
    IsIso (((adj.projectionMap G' T T' δ).app K).app M) := by
  have hZ : IsIso (adj.counit.app (F.obj Z)) := by
    have : IsIso (F.map (adj.unit.app Z) ≫ adj.counit.app (F.obj Z)) := by
      rw [adj.left_triangle_components Z]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (F.map (adj.unit.app Z)) _
  have hN : IsIso (adj.counit.app ((T'.obj (F.obj K)).obj M)) := by
    have h := adj.counit.naturality e.hom
    dsimp at h
    have : IsIso (adj.counit.app ((T'.obj (F.obj K)).obj M) ≫ e.hom) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  rw [projectionMap_app_app, homEquiv_counit]
  have : IsIso (adj.counit.app
      ((((((Functor.whiskeringLeft₂ D).obj F).obj (𝟭 D)).obj T').obj K).obj M)) := hN
  infer_instance

end LeftAdjoint

section RightAdjoint

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The right adjoint projection map `T_D (G M) L ⟶ G (T_C M (F L))` attached to an adjunction
`F ⊣ G` and a comparison `φ : F (T_D a b) ⟶ T_C (F a) (F b)`, as a natural transformation of
bifunctors `C ⥤ D ⥤ D`. It is the transpose along `adj` of
`(φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L)`, see
`CategoryTheory.Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app`. -/
def rightAdjointProjectionMap :
    G ⋙ T_D ⟶ (postcompose₂.obj G).obj ((((whiskeringLeft₂ C).obj (𝟭 C)).obj F).obj T_C) where
  app M :=
    { app L := adj.homEquiv _ _
        ((φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L))
      naturality L L' f := by
        dsimp
        rw [← homEquiv_naturality_left, ← homEquiv_naturality_right]
        congr 1
        simpa using (φ.app (G.obj M)).naturality_assoc f ((T_C.map (adj.counit.app M)).app _) }
  naturality M M' f := by
    ext L
    dsimp
    rw [← homEquiv_naturality_left, ← homEquiv_naturality_right]
    congr 1
    simpa [← NatTrans.comp_app, ← Functor.map_comp] using NatTrans.naturality_app_assoc φ L
      (G.map f) ((T_C.map (adj.counit.app M')).app (F.obj L))

lemma rightAdjointProjectionMap_app_app (M : C) (L : D) :
    ((adj.rightAdjointProjectionMap φ).app M).app L = adj.homEquiv _ _
      ((φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L)) :=
  rfl

/-- The transpose along `adj : F ⊣ G` of the right adjoint projection map
`T_D (G M) L ⟶ G (T_C M (F L))` is the composite
```
F (T_D (G M) L) --φ--> T_C (F (G M)) (F L)
        \                    |
         \                   | T_C (ε_M) (𝟙 (F L))
       transpose             v
           ----------->  T_C M (F L)
```
where the long edge is `(adj.homEquiv _ _).symm` of the right adjoint projection map.
-/
@[simp, reassoc]
lemma homEquiv_symm_rightAdjointProjectionMap_app_app (M : C) (L : D) :
    (adj.homEquiv _ _).symm (((adj.rightAdjointProjectionMap φ).app M).app L) =
      (φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L) :=
  Equiv.symm_apply_apply _ _

/-- The counit form of `CategoryTheory.Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app`:
applying `F` to the right adjoint projection map and composing with the counit of `adj` gives
`φ` followed by the counit of `adj` in the first variable. -/
@[reassoc]
lemma map_rightAdjointProjectionMap_app_app_comp_counit (M : C) (L : D) :
    F.map (((adj.rightAdjointProjectionMap φ).app M).app L) ≫ adj.counit.app _ =
      (φ.app (G.obj M)).app L ≫ (T_C.map (adj.counit.app M)).app (F.obj L) := by
  simpa [homEquiv_counit] using adj.homEquiv_symm_rightAdjointProjectionMap_app_app φ M L

end RightAdjoint

end CategoryTheory.Adjunction
