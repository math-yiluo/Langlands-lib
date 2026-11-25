/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Plus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# The plus construction and multiequalizers

For a cover `S` of `X` and a presheaf `P`, we relate the map `J.toPlus P : P ⟶ P⁺` to the
multiequalizer `multiequalizer (S.index P)` appearing in the sheaf condition.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Cover.multiequalizerFunctor`: the functor
  `P ↦ multiequalizer (S.index P)`.
* `CategoryTheory.GrothendieckTopology.Cover.toMultiequalizerNatTrans`: the maps
  `S.toMultiequalizer P`, as a natural transformation in `P`.

## Main results

* `CategoryTheory.GrothendieckTopology.toMultiequalizer_ι_diagram`: the map `P(X) ⟶ P⁺(X)`
  factors through `S.toMultiequalizer P`.
* `CategoryTheory.GrothendieckTopology.ι_diagram_toMultiequalizer_plusObj`: the `S`-component
  of `P⁺(X)` followed by `S.toMultiequalizer P⁺` is induced by `J.toPlus P`.
-/

@[expose] public section

universe w w' u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type w} [Category.{w'} D]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

namespace Cover

variable {X : C} (S : J.Cover X)

variable (D) in
/-- The functor `P ↦ multiequalizer (S.index P)` for a cover `S` of `X`. -/
@[simps obj]
noncomputable def multiequalizerFunctor : (Cᵒᵖ ⥤ D) ⥤ D where
  obj P := multiequalizer (S.index P)
  map η := (J.diagramNatTrans η X).app (op S)

@[reassoc (attr := simp)]
lemma multiequalizerFunctor_map_ι {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (I : S.Arrow) :
    (S.multiequalizerFunctor D).map η ≫ Multiequalizer.ι (S.index Q) I =
      Multiequalizer.ι (S.index P) I ≫ η.app (op I.Y) :=
  Multiequalizer.lift_ι _ _ _ _ _

/-- The maps `S.toMultiequalizer P` are natural in the presheaf `P`. -/
@[reassoc]
lemma toMultiequalizer_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η.app (op X) ≫ S.toMultiequalizer Q =
      S.toMultiequalizer P ≫ (S.multiequalizerFunctor D).map η :=
  Multiequalizer.hom_ext _ _ _ fun I ↦ by simp

variable (D) in
/-- The maps `S.toMultiequalizer P : P(X) ⟶ multiequalizer (S.index P)`, as a natural
transformation in the presheaf `P`. -/
@[simps]
noncomputable def toMultiequalizerNatTrans :
    (evaluation Cᵒᵖ D).obj (op X) ⟶ S.multiequalizerFunctor D where
  app P := S.toMultiequalizer P
  naturality _ _ η := S.toMultiequalizer_naturality η

end Cover

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

lemma plusObj_map (P : Cᵒᵖ ⥤ D) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (J.plusObj P).map f = colimMap (J.diagramPullback P f.unop) ≫ colimit.pre _ _ :=
  rfl

lemma toPlus_app (P : Cᵒᵖ ⥤ D) (X : Cᵒᵖ) :
    (J.toPlus P).app X =
      (⊤ : J.Cover X.unop).toMultiequalizer P ≫ colimit.ι (J.diagram P X.unop) (op ⊤) :=
  rfl

/-- The map `P(X) ⟶ P⁺(X)` factors as `S.toMultiequalizer P` followed by the coprojection
of the `S`-component, for every cover `S` of `X`:
```
P(X) ──S.toMultiequalizer P──▶ multiequalizer (S.index P)
    ╲                                   │
     ╲ (J.toPlus P).app (op X)          │ colimit.ι _ (op S)
      ╲                                 ▼
       ╰─────────────────────────────▶ P⁺(X)
```
-/
@[reassoc]
lemma toMultiequalizer_ι_diagram (P : Cᵒᵖ ⥤ D) {X : C} (S : J.Cover X) :
    S.toMultiequalizer P ≫ colimit.ι (J.diagram P X) (op S) = (J.toPlus P).app (op X) := by
  rw [toPlus_app, ← colimit.w _ (homOfLE (le_top : S ≤ ⊤)).op, ← Category.assoc]
  congr 1
  exact Multiequalizer.hom_ext _ _ _ fun I ↦ by simp [Cover.Arrow.map]

/-- The `S`-component `multiequalizer (S.index P) ⟶ P⁺(X)` of `P⁺(X)`, followed by the map
`S.toMultiequalizer P⁺`, is the map of multiequalizers induced by `J.toPlus P : P ⟶ P⁺`:
```
multiequalizer (S.index P) ──colimit.ι _ (op S)──▶ P⁺(X)
           ╲                                         │
            ╲ (S.multiequalizerFunctor D)            │ S.toMultiequalizer P⁺
             ╲    .map (J.toPlus P)                  ▼
              ╰────────────────────────▶ multiequalizer (S.index P⁺)
```
-/
@[reassoc]
lemma ι_diagram_toMultiequalizer_plusObj (P : Cᵒᵖ ⥤ D) {X : C} (S : J.Cover X) :
    colimit.ι (J.diagram P X) (op S) ≫ S.toMultiequalizer (J.plusObj P) =
      (S.multiequalizerFunctor D).map (J.toPlus P) := by
  refine Multiequalizer.hom_ext _ _ _ fun (I : S.Arrow) ↦ ?_
  simp only [Category.assoc, Cover.toMultiequalizer_ι, plusObj_map, ι_colimMap_assoc,
    colimit.ι_pre, Cover.multiequalizerFunctor_map_ι, toPlus_app, Quiver.Hom.unop_op,
    Functor.op_obj, unop_op]
  rw [← colimit.w (J.diagram P I.Y)
    (homOfLE (x := ⊤) (y := (J.pullback I.f).obj S) (S.1.pullback_eq_top_of_mem I.hf).ge).op,
    ← Category.assoc, ← Category.assoc]
  congr 1
  refine Multiequalizer.hom_ext _ _ _ fun K ↦ ?_
  have := Multiequalizer.condition (S.index P)
    { fst := ⟨K.Y, K.f ≫ I.f, S.1.downward_closed I.hf K.f⟩, snd := I, r.Z := K.Y,
      r.g₁ := 𝟙 K.Y, r.g₂ := K.f }
  simp only [Cover.index_fst, Cover.index_snd, Cover.shape, op_id, P.map_id] at this
  simp only [Functor.comp_obj, Functor.op_obj, diagramPullback_app, Cover.Arrow.base,
    homOfLE_leOfHom, diagram_map, Quiver.Hom.unop_op, Cover.Arrow.map, Category.assoc,
    limit.lift_π, Multifork.ofι_π_app]
  exact (Category.comp_id _).symm.trans this

end CategoryTheory.GrothendieckTopology
