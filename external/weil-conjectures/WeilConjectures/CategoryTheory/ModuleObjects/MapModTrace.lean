/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive

/-!
# Traces of monoidal adjunctions on module objects

Let `adj : F ⊣ G` be a monoidal adjunction between preadditive monoidal categories, with unit
`u : 𝟭 ⟶ F ⋙ G` a monomorphism at every object. Let `ρ i : F ⋙ G ⟶ F ⋙ G` be finitely many
*monoidal* natural transformations fixing the unit (`u ≫ ρ i = u`), and `t : F ⋙ G ⟶ 𝟭` a natural
transformation factoring their sum through the unit: `t ≫ u = ∑ i, ρ i`. In the application `F ⊣ G`
is `g^* ⊣ g_*` for a finite étale Galois covering `g` with group `Γ`, the `ρ i` are the action of
`Γ` and `t` is the trace.

Then `t` and the `ρ i` are linear over every algebra object `R`, for the module structure of
`G (F M)` through the unit `R ⟶ G (F R)`: they lift to natural transformations of the functor
`F.mapMod R ⋙ G.mapMod (F R) ⋙ Mod.comap (u R)` on `R`-module objects
(`CategoryTheory.Adjunction.mapModTrace`, `CategoryTheory.Adjunction.mapModAction`), with the same
identities with respect to the unit of the lifted adjunction `Adjunction.mapModAdjunction`.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory MonObj Functor.LaxMonoidal

namespace CategoryTheory.Adjunction

open scoped Obj

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  {D : Type*} [Category D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (R : C) [MonObj R]

/-- The functor `M ↦ G (F M)` on `R`-module objects underlying the lifted adjunction. -/
abbrev mapModComp : Mod C R ⥤ Mod C R :=
  F.mapMod R ⋙ G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)

omit [Preadditive C] [MonoidalPreadditive C] in
/-- The action of `R` on `G (F M)` through the unit is `u ▷ _ ≫ μ ≫ (F ⋙ G).map γ`. -/
lemma act_mapModComp_obj (M : Mod C R) :
    γ[R, ((adj.mapModComp R).obj M).X] =
      adj.unit.app R ▷ G.obj (F.obj M.X) ≫ Functor.LaxMonoidal.μ (F ⋙ G) R M.X ≫
        (F ⋙ G).map γ[R, M.X] := by
  rw [Functor.LaxMonoidal.comp_μ, Functor.comp_map, assoc, ← G.map_comp]
  rfl

variable {adj} {ι : Type*} {ρ : ι → (F ⋙ G ⟶ F ⋙ G)} [∀ i, NatTrans.IsMonoidal (ρ i)]
  (hρ : ∀ i, adj.unit ≫ ρ i = adj.unit)

omit [Preadditive C] [MonoidalPreadditive C] in
include hρ in
lemma act_comp_app_eq (i : ι) (M : Mod C R) :
    γ[R, ((adj.mapModComp R).obj M).X] ≫ (ρ i).app M.X =
      R ◁ (ρ i).app M.X ≫ γ[R, ((adj.mapModComp R).obj M).X] := by
  have h := congr_app (hρ i) R
  simp only [NatTrans.comp_app] at h
  rw [act_mapModComp_obj, assoc, assoc, (ρ i).naturality, NatTrans.IsMonoidal.tensor_assoc]
  simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h, id_comp]
  erw [comp_id]

/-- The action `ρ i` lifted to `R`-module objects. -/
@[simps]
def mapModAction (i : ι) : adj.mapModComp R ⟶ adj.mapModComp R where
  app M := Mod.homMk ((ρ i).app M.X) (act_comp_app_eq R hρ i M)
  naturality _ _ φ := Mod.hom_ext _ _ ((ρ i).naturality φ.hom)

variable [Fintype ι] {t : F ⋙ G ⟶ 𝟭 C} (ht : t ≫ adj.unit = ∑ i, ρ i)
  [∀ X, Mono (adj.unit.app X)]

include hρ ht in
lemma act_comp_trace_app_eq (M : Mod C R) :
    γ[R, ((adj.mapModComp R).obj M).X] ≫ t.app M.X = R ◁ t.app M.X ≫ γ[R, M.X] := by
  have ht' := congr_app ht M.X
  simp only [NatTrans.comp_app, NatTrans.app_sum] at ht'
  rw [← cancel_mono (adj.unit.app M.X), assoc, ht', Preadditive.comp_sum]
  simp only [act_comp_app_eq R hρ]
  rw [← Preadditive.sum_comp, ← whiskerLeft_sum, ← ht',
    MonoidalCategory.whiskerLeft_comp_assoc, assoc]
  congr 1
  have hu := NatTrans.IsMonoidal.tensor (τ := adj.unit) R M.X
  simp only [Functor.LaxMonoidal.id_μ, id_comp] at hu
  rw [act_mapModComp_obj]
  erw [adj.unit.naturality, hu]
  rw [tensorHom_def', assoc, assoc]
  rfl

/-- The trace `t` lifted to `R`-module objects. -/
@[simps]
def mapModTrace : adj.mapModComp R ⟶ 𝟭 (Mod C R) where
  app M := Mod.homMk (t.app M.X) (act_comp_trace_app_eq R hρ ht M)
  naturality _ _ φ := Mod.hom_ext _ _ (t.naturality φ.hom)

include hρ ht in
/-- The lifted trace followed by the lifted unit is the sum of the lifted actions. -/
lemma mapModTrace_comp_unit :
    mapModTrace R hρ ht ≫ (adj.mapModAdjunction R).unit = ∑ i, mapModAction R hρ i := by
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  have ht' := congr_app ht M.X
  simp only [NatTrans.comp_app, NatTrans.app_sum] at ht'
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.id_obj, mapModTrace_app, Mod.comp_hom',
    Mod.homMk_hom, mapModAdjunction_unit_app_hom, ht', NatTrans.app_sum]
  exact ((Mod.forget (D := C) R).map_sum (fun i ↦ (mapModAction R hρ i).app M) Finset.univ).symm

include hρ ht in
/-- The lifted unit followed by the lifted trace is multiplication by `d` if `u ≫ t = d • 𝟙`. -/
lemma unit_comp_mapModTrace {d : ℕ} (hd : adj.unit ≫ t = d • 𝟙 _) :
    (adj.mapModAdjunction R).unit ≫ mapModTrace R hρ ht = d • 𝟙 _ := by
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  have hd' := congr_app hd M.X
  simp only [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app] at hd'
  simp only [Functor.id_obj, NatTrans.comp_app, Functor.comp_obj, mapModTrace_app, Mod.comp_hom',
    mapModAdjunction_unit_app_hom, Mod.homMk_hom, hd', NatTrans.app_nsmul, NatTrans.id_app,
    Mod.nsmul_hom, Mod.id_hom']

end CategoryTheory.Adjunction
