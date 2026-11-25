/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The composition isomorphism of pushforwards of sheaves is monoidal

For continuous functors `F : C ⥤ D`, `G : D ⥤ E` and `FG ≅ F ⋙ G`, the pushforwards of sheaves
`F_*`, `G_*` and `FG_*` are lax monoidal, and the identification `G_* ⋙ F_* ≅ FG_*` of
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` is a monoidal natural isomorphism.
Its compatibility with the units is
`CategoryTheory.Functor.ε_sheafPushforwardContinuous_of_iso_comp`; this file proves the
compatibility with the tensor products, by reducing to underlying presheaves.

## Main results

- `CategoryTheory.Sheaf.hom_ext_of_μ_comp`: morphisms out of a tensor product of sheaves are
  determined on underlying presheaves after `μ : P ⊗ Q ⟶ (P ⊗ Q).obj` of `sheafToPresheaf`.
- `CategoryTheory.Functor.μ_sheafPushforwardContinuous_of_iso_comp`: the tensor axiom.
- `CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`: the identification
  `G_* ⋙ F_* ≅ FG_*` is monoidal.

## Implementation notes

These results belong next to `CategoryTheory.Functor.ε_sheafPushforwardContinuous_of_iso_comp`
in `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`; they are kept in a separate file
because that file is imported by most of the project.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

section

variable {C : Type*} [Category C] {A : Type*} [Category A] [MonoidalCategory A]
  {J : GrothendieckTopology C} [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] Sheaf.monoidalCategory

/-- Two morphisms out of a tensor product `P ⊗ Q` of sheaves agree as soon as they agree on
underlying presheaves after the map `μ : P.obj ⊗ Q.obj ⟶ (P ⊗ Q).obj` of the lax monoidal functor
`sheafToPresheaf`: this map is adjoint to the isomorphism
`sheafify (P.obj ⊗ Q.obj) ≅ sheafify P.obj ⊗ sheafify Q.obj ≅ P ⊗ Q`. That is, `a = b` as
soon as the two composites

```
P.obj ⊗ Q.obj --μ--> (P ⊗ Q).obj ==a.obj==> G.obj
                                 ==b.obj==>
```

agree. -/
lemma Sheaf.hom_ext_of_μ_comp {P Q G : Sheaf J A} {a b : P ⊗ Q ⟶ G}
    (h : μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map a =
      μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map b) : a = b := by
  have e (c : P ⊗ Q ⟶ G) : ((sheafificationAdjunction J A).homEquiv _ _).symm
      (μ (sheafToPresheaf J A) P Q ≫ (sheafToPresheaf J A).map c) =
        (δ (presheafToSheaf J A) P.obj Q.obj ≫
          ((sheafificationAdjunction J A).counit.app P ⊗ₘ
            (sheafificationAdjunction J A).counit.app Q)) ≫ c := by
    rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
      Category.assoc, Adjunction.map_μ_comp_counit_app_tensor_assoc, Category.assoc]
    rfl
  rw [← cancel_epi (δ (presheafToSheaf J A) P.obj Q.obj ≫
          ((sheafificationAdjunction J A).counit.app P ⊗ₘ
            (sheafificationAdjunction J A).counit.app Q)), ← e, ← e, h]

end

namespace Functor

variable {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
  (A : Type*) [Category A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [F.IsContinuous J K]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]

attribute [local instance] Sheaf.monoidalCategory

/-- The tensor map `μ` of the lax monoidal pushforward `F_*` of sheaves, read on underlying
presheaves after `μ` of the lax monoidal functor `sheafToPresheaf`, is the restriction along
`F.op` of `μ` of `sheafToPresheaf`. Writing `ι` for `sheafToPresheaf`, the square

```
ι (F_* P) ⊗ ι (F_* Q) --μ_ι--> ι (F_* P ⊗ F_* Q) --ι μ_{F_*}--> ι (F_* (P ⊗ Q))
          ‖                                                          ‖
(ι P) ∘ F ⊗ (ι Q) ∘ F ----μ----> (ι P ⊗ ι Q) ∘ F -----μ_ι ∘ F-----> ι (P ⊗ Q) ∘ F
```

commutes, where `- ∘ F` is the restriction `(whiskeringLeft _ _ A).obj F.op` and the bottom
`μ` is its tensor map. -/
lemma μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous (P Q : Sheaf K A) :
    μ (sheafToPresheaf J A) ((F.sheafPushforwardContinuous A J K).obj P)
        ((F.sheafPushforwardContinuous A J K).obj Q) ≫
      (sheafToPresheaf J A).map (μ (F.sheafPushforwardContinuous A J K) P Q) =
    μ ((whiskeringLeft _ _ A).obj F.op) P.obj Q.obj ≫
      ((whiskeringLeft _ _ A).obj F.op).map (μ (sheafToPresheaf K A) P Q) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom) P Q
  rw [sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app, comp_μ, comp_μ] at h
  simpa using h.symm

/-- The componentwise form of
`CategoryTheory.Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous`. -/
@[reassoc]
lemma μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app (P Q : Sheaf K A) (U : Cᵒᵖ) :
    (μ (sheafToPresheaf J A) ((F.sheafPushforwardContinuous A J K).obj P)
        ((F.sheafPushforwardContinuous A J K).obj Q)).app U ≫
      (μ (F.sheafPushforwardContinuous A J K) P Q).hom.app U =
    (μ (sheafToPresheaf K A) P Q).app (F.op.obj U) := by
  have h := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous F A J K P Q) U
  simp only [NatTrans.comp_app] at h
  exact h.trans (Category.id_comp _)

variable {A J K} in
/-- For continuous functors `F`, `G` and `FG ≅ F ⋙ G`, the identification `G_* ⋙ F_* ≅ FG_*`
of `CategoryTheory.Functor.sheafPushforwardContinuousComp'` is compatible with the tensor maps
`μ` of the lax monoidal pushforwards: the square

```
F_* G_* X ⊗ F_* G_* Y --μ_F--> F_* (G_* X ⊗ G_* Y) --F_* μ_G--> F_* G_* (X ⊗ Y)
        |                                                             |
     c_X ⊗ c_Y                                                     c_{X ⊗ Y}
        v                                                             v
  FG_* X ⊗ FG_* Y ---------------------μ_FG----------------------> FG_* (X ⊗ Y)
```

commutes, where `c : G_* ⋙ F_* ≅ FG_*` is `sheafPushforwardContinuousComp' e`. -/
lemma μ_sheafPushforwardContinuous_of_iso_comp {E : Type*} [Category E]
    (L : GrothendieckTopology E) [(L.W (A := A)).IsMonoidal] [HasWeakSheafify L A]
    {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG) [hF : F.IsContinuous J K]
    [hG : G.IsContinuous K L] [hFG : FG.IsContinuous J L] (X Y : Sheaf L A) :
    μ (F.sheafPushforwardContinuous A J K) ((G.sheafPushforwardContinuous A K L).obj X)
        ((G.sheafPushforwardContinuous A K L).obj Y) ≫
      (F.sheafPushforwardContinuous A J K).map (μ (G.sheafPushforwardContinuous A K L) X Y) ≫
        (sheafPushforwardContinuousComp' e A J K L).hom.app (X ⊗ Y) =
      ((sheafPushforwardContinuousComp' e A J K L).hom.app X ⊗ₘ
        (sheafPushforwardContinuousComp' e A J K L).hom.app Y) ≫
        μ (FG.sheafPushforwardContinuous A J L) X Y := by
  apply Sheaf.hom_ext_of_μ_comp
  ext U
  have hX := (μ (sheafToPresheaf L A) X Y).naturality (e.inv.app U.unop).op
  simp only [ObjectProperty.ι_obj, CategoryTheory.Monoidal.tensorObj_obj, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    sheafPushforwardContinuous_map_hom_app, sheafPushforwardContinuousComp'_hom_app_hom_app,
    comp_obj] at hX ⊢
  have h2 := congr_app (μ_natural (sheafToPresheaf J A)
      ((sheafPushforwardContinuousComp' e A J K L).hom.app X)
      ((sheafPushforwardContinuousComp' e A J K L).hom.app Y)) U
  simp only [NatTrans.comp_app] at h2
  erw [← reassoc_of% h2, μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app]
  simpa [μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc] using hX.symm

variable {A J K} in
/-- For continuous functors `F`, `G` and `FG ≅ F ⋙ G`, the identification `G_* ⋙ F_* ≅ FG_*`
of `CategoryTheory.Functor.sheafPushforwardContinuousComp'` is a monoidal natural
transformation. -/
instance isMonoidal_sheafPushforwardContinuousComp'_hom {E : Type*} [Category E]
    {L : GrothendieckTopology E} [(L.W (A := A)).IsMonoidal] [HasWeakSheafify L A]
    {F : C ⥤ D} {G : D ⥤ E} {FG : C ⥤ E} (e : F ⋙ G ≅ FG) [F.IsContinuous J K]
    [G.IsContinuous K L] [FG.IsContinuous J L] :
    NatTrans.IsMonoidal (sheafPushforwardContinuousComp' e A J K L).hom where
  unit := by
    rw [comp_ε, Category.assoc]
    exact (ε_sheafPushforwardContinuous_of_iso_comp A J K L e).symm
  tensor X Y := by
    rw [comp_μ, Category.assoc]
    exact μ_sheafPushforwardContinuous_of_iso_comp L e X Y

end Functor

end CategoryTheory

