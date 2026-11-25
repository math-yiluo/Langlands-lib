/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The projection formula for left Kan extensions

For `L : C ⥤ D` and functors `F : C ⥤ H`, `G : D ⥤ H` with values in a monoidal category, the
pointwise tensor product gives a canonical map `Lan_L(F ⊗ (L ⋙ G)) ⟶ Lan_L F ⊗ G`
(`CategoryTheory.Functor.lanProjectionMap`). It is an isomorphism at `Y` when the comma
category `CostructuredArrow L Y` receives a final functor from a discrete category whose
structure maps are isomorphisms, and tensoring with `G Y` preserves the corresponding
coproducts (`CategoryTheory.Functor.isIso_lanProjectionMap_app`). For the localization functor
of an étale morphism, these are the lifts through the morphism, and this is the presheaf-level
projection formula for extension by zero.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory
namespace CategoryTheory.Functor

variable {C D H : Type*} [Category C] [Category D] [Category H] [MonoidalCategory H]
  (L : C ⥤ D) [∀ F : C ⥤ H, L.HasPointwiseLeftKanExtension F]

/-- The projection map `Lan(F ⊗ (L ⋙ G)) ⟶ Lan F ⊗ G`: the map adjoint to
`F ⊗ (L ⋙ G) ⟶ (L ⋙ Lan F) ⊗ (L ⋙ G)`, the unit of `Lan ⊣ (L ⋙ ·)` tensored with the identity.
-/
noncomputable def lanProjectionMap (F : C ⥤ H) (G : D ⥤ H) :
    L.lan.obj (F ⊗ (L ⋙ G)) ⟶ L.lan.obj F ⊗ G :=
  (L.lanAdjunction H).homEquiv _ _ |>.symm
    ((L.lanAdjunction H).unit.app F ⊗ₘ 𝟙 (L ⋙ G))

/-- The projection map restricted along `L` is the unit tensored with the identity: for `c : C`
the square
```
  F c ⊗ G (L c) ──── unit ────▶ Lan(F ⊗ (L ⋙ G))(L c)
        │                               │
   unit ⊗ 𝟙                       lanProjectionMap
        ▼                               ▼
  (Lan F)(L c) ⊗ G (L c) ═══════ (Lan F)(L c) ⊗ G (L c)
```
commutes. -/
lemma lanUnit_app_comp_lanProjectionMap_app (F : C ⥤ H) (G : D ⥤ H) (c : C) :
    (L.lanUnit.app (F ⊗ (L ⋙ G))).app c ≫ (L.lanProjectionMap F G).app (L.obj c) =
      (L.lanUnit.app F).app c ⊗ₘ 𝟙 (G.obj (L.obj c)) := by
  have h := (L.lanAdjunction H).homEquiv_unit (F ⊗ (L ⋙ G)) (L.lan.obj F ⊗ G)
    (L.lanProjectionMap F G)
  have h0 : (L.lanAdjunction H).homEquiv _ _ (L.lanProjectionMap F G) =
      (L.lanAdjunction H).unit.app F ⊗ₘ 𝟙 (L ⋙ G) := by
    rw [lanProjectionMap, Equiv.apply_symm_apply]
  have h' := congr_app (h.symm.trans h0) c
  rw [lanAdjunction_unit] at h'
  exact h'

/-- The projection map is natural in both variables. -/
lemma lanProjectionMap_naturality {F F' : C ⥤ H} {G G' : D ⥤ H} (φ : F ⟶ F') (ψ : G ⟶ G') :
    L.lan.map (φ ⊗ₘ Functor.whiskerLeft L ψ) ≫ L.lanProjectionMap F' G' =
      L.lanProjectionMap F G ≫ (L.lan.map φ ⊗ₘ ψ) := by
  apply ((L.lanAdjunction H).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [lanProjectionMap, Equiv.apply_symm_apply]
  ext c
  simp only [NatTrans.comp_app, Monoidal.tensorHom_app, whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, NatTrans.id_app, tensorHom_comp_tensorHom, Category.comp_id,
    Category.id_comp]
  congr 1
  exact congr_app ((L.lanAdjunction H).unit.naturality φ) c

/-- The legs of the cocone exhibiting `Lan F ⊗ G` at `Y` as a colimit. -/
noncomputable def lanProjectionCocone (F : C ⥤ H) (G : D ⥤ H) (Y : D) :
    Cocone (CostructuredArrow.proj L Y ⋙ (F ⊗ (L ⋙ G))) where
  pt := (L.lan.obj F).obj Y ⊗ G.obj Y
  ι :=
    { app := fun g ↦ ((L.lanUnit.app F).app g.left ≫ (L.lan.obj F).map g.hom) ⊗ₘ G.map g.hom
      naturality := fun g g' φ ↦ by
        have h := CostructuredArrow.w φ
        simp only [Functor.comp_obj, Functor.comp_map,
          CostructuredArrow.proj_map, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
        rw [← h]
        change (F.map φ.left ⊗ₘ G.map (L.map φ.left)) ≫ _ = _
        rw [tensorHom_comp_tensorHom, Functor.map_comp, Functor.map_comp, ← Category.assoc,
          ← Category.assoc]
        congr 2
        exact (L.lanUnit.app F).naturality φ.left }

/-- **The projection formula for pointwise left Kan extensions.** If the comma category
`CostructuredArrow L Y` receives a final functor `s` from a discrete category `ι` whose objects
have invertible structure maps `L (s i) ≅ Y`, and `- ⊗ G Y` preserves `ι`-indexed coproducts,
then the projection map
```
  Lan(F ⊗ (L ⋙ G))(Y) ⟶ (Lan F)(Y) ⊗ G(Y)
```
is an isomorphism: both sides are `⨁_i F(s i) ⊗ G(Y)`. -/
theorem isIso_lanProjectionMap_app (F : C ⥤ H) (G : D ⥤ H) (Y : D) {ι : Type*}
    (s : Discrete ι ⥤ CostructuredArrow L Y) [s.Final] (hs : ∀ i, IsIso (s.obj i).hom)
    [HasColimitsOfShape (Discrete ι) H]
    [PreservesColimitsOfShape (Discrete ι) (tensorRight (G.obj Y))] :
    IsIso ((L.lanProjectionMap F G).app Y) := by
  let cF := (LeftExtension.mk _ (L.leftKanExtensionUnit F)).coconeAt Y
  have hF : IsColimit cF := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit F Y
  have hFs : IsColimit (cF.whisker s) := (Final.isColimitWhiskerEquiv s cF).symm hF
  have hT := isColimitOfPreserves (tensorRight (G.obj Y)) hFs
  let e : (s ⋙ CostructuredArrow.proj L Y ⋙ F) ⋙ tensorRight (G.obj Y) ≅
      s ⋙ CostructuredArrow.proj L Y ⋙ (F ⊗ (L ⋙ G)) :=
    Discrete.natIso fun i ↦
      whiskerLeftIso (F.obj (s.obj i).left) (G.mapIso (asIso (s.obj i).hom)).symm
  have h₁ := (IsColimit.precomposeInvEquiv e _).symm hT
  have h₂ : IsColimit ((L.lanProjectionCocone F G Y).whisker s) := by
    refine IsColimit.ofIsoColimit h₁ (Cocone.ext (Iso.refl _) fun i ↦ ?_)
    simp [e, cF, lanProjectionCocone, tensorHom_def']
    rfl
  have hc := (Final.isColimitWhiskerEquiv s _) h₂
  let cP := (LeftExtension.mk _ (L.leftKanExtensionUnit (F ⊗ (L ⋙ G)))).coconeAt Y
  have hP : IsColimit cP := L.isPointwiseLeftKanExtensionLeftKanExtensionUnit _ Y
  have heq : (L.lanProjectionMap F G).app Y = (hP.coconePointUniqueUpToIso hc).hom := by
    refine hP.hom_ext fun g ↦ ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    change ((L.lanUnit.app _).app g.left ≫ (L.lan.obj _).map g.hom) ≫ _ = _
    rw [Category.assoc, (L.lanProjectionMap F G).naturality, ← Category.assoc,
      lanUnit_app_comp_lanProjectionMap_app]
    change (_ ⊗ₘ 𝟙 _) ≫ ((L.lan.obj F).map g.hom ⊗ₘ G.map g.hom) = _
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    rfl
  rw [heq]
  infer_instance

end CategoryTheory.Functor
