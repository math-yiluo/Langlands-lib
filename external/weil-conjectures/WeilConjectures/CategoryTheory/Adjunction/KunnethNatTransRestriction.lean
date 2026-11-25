/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethNatTrans

/-!

# Restriction of Künneth maps

Let `F ⊣ G` and `F' ⊣ G'` be adjunctions between monoidal categories, `W` and `W'` oplax
monoidal functors ("restrictions") and `β : W ⋙ F' ≅ F ⋙ W'` an isomorphism compatible with the
oplax structure maps, with exchange morphism `exchangeRight adj adj' β : G ⋙ W ⟶ W' ⋙ G'`.
This file shows that `W` applied to a Künneth map of `F ⊣ G`
(`CategoryTheory.Adjunction.kunnethNatTrans`), followed by the exchange morphism, is a Künneth map
of `F' ⊣ G'`, up to the structure maps of `W` and `W'` and comparison morphisms of the
ingredients (`CategoryTheory.Adjunction.map_kunnethNatTrans_app_comp_exchangeRight_app`). In
particular, if `W` and `W'` are strong monoidal, the comparisons and the exchange morphism are
isomorphisms and the restricted Künneth map is an isomorphism, so is `W` of the original
Künneth map (`CategoryTheory.Adjunction.isIso_map_kunnethNatTrans_app`).

In the application, `W` and `W'` are derived pullbacks along an open immersion, and the exchange
morphism is a base change morphism.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  {W : D ⥤ D'} {W' : C ⥤ C'} (β : W ⋙ F' ≅ F ⋙ W')

/-- The transpose along `F' ⊣ G'` of `W` of the transpose `A ⟶ G B` of `f : F A ⟶ B`, followed by
the exchange morphism of `β`, is `β` followed by `W' f`. -/
lemma homEquiv_symm_map_homEquiv_comp_exchangeRight_app {A : D} {B : C} (f : F.obj A ⟶ B) :
    (adj'.homEquiv _ _).symm (W.map (adj.homEquiv _ _ f) ≫ (exchangeRight adj adj' β).app B) =
      β.hom.app A ≫ W'.map f := by
  rw [← homEquiv_hom_app_comp_map_counit, ← homEquiv_naturality_left, Equiv.symm_apply_apply]
  have h := β.hom.naturality_assoc (adj.homEquiv _ _ f) (W'.map (adj.counit.app B))
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [h, ← W'.map_comp]
  simp [homEquiv_unit]

variable [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
  [F.OplaxMonoidal] [F'.OplaxMonoidal] [W.OplaxMonoidal] [W'.OplaxMonoidal]
  {𝒳 : Type u₅} [Category.{v₅} 𝒳] {P : 𝒳 ⥤ D} {Q : 𝒳 ⥤ C} (e : P ⋙ F ≅ Q)
  {C₀ : D} {D₀ : C} (c : F.obj C₀ ⟶ D₀)
  {𝒳' : Type u₆} [Category.{v₆} 𝒳'] {P' : 𝒳' ⥤ D'} {Q' : 𝒳' ⥤ C'} (e' : P' ⋙ F' ≅ Q')
  {C₀' : D'} {D₀' : C'} (c' : F'.obj C₀' ⟶ D₀')

/-- **Restriction of Künneth maps**: if `β : W ⋙ F' ≅ F ⋙ W'` is compatible with the oplax
structure maps and the comparison morphisms `a₁, a₂, b₁, b₂` of the ingredients of the Künneth
maps are compatible with `e`, `e'`, `c` and `c'` through `β`, then `W` of the Künneth map of
`F ⊣ G` at `M`, followed by the exchange morphism of `β` and the structure maps of `W'`, is the
structure map of `W` followed by the Künneth map of `F' ⊣ G'` at `M'`. -/
lemma map_kunnethNatTrans_app_comp_exchangeRight_app
    (hβ : ∀ A B : D, β.hom.app (A ⊗ B) ≫ W'.map (δ F A B) ≫ δ W' (F.obj A) (F.obj B) =
      F'.map (δ W A B) ≫ δ F' (W.obj A) (W.obj B) ≫ (β.hom.app A ⊗ₘ β.hom.app B))
    {M : 𝒳} {M' : 𝒳'} (a₁ : W.obj (P.obj M) ⟶ P'.obj M') (a₂ : W.obj C₀ ⟶ C₀')
    (b₁ : W'.obj (Q.obj M) ⟶ Q'.obj M') (b₂ : W'.obj D₀ ⟶ D₀')
    (h₁ : β.hom.app (P.obj M) ≫ W'.map (e.hom.app M) ≫ b₁ = F'.map a₁ ≫ e'.hom.app M')
    (h₂ : β.hom.app C₀ ≫ W'.map c ≫ b₂ = F'.map a₂ ≫ c') :
    W.map ((adj.kunnethNatTrans e c).app M) ≫ (exchangeRight adj adj' β).app _ ≫
        G'.map (δ W' _ _ ≫ (b₁ ⊗ₘ b₂)) =
      (δ W _ _ ≫ (a₁ ⊗ₘ a₂)) ≫ (adj'.kunnethNatTrans e' c').app M' := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [kunnethNatTrans_app, kunnethNatTrans_app]
  dsimp only [Functor.comp_obj, Functor.flip_obj_obj, curriedTensor_obj_obj]
  rw [← Category.assoc, homEquiv_naturality_right_symm,
    homEquiv_symm_map_homEquiv_comp_exchangeRight_app, homEquiv_naturality_left_symm,
    Equiv.symm_apply_apply, W'.map_comp, F'.map_comp]
  simp only [Category.assoc]
  rw [← δ_natural_assoc, reassoc_of% hβ]
  rw [← δ_natural_assoc]
  simp only [tensorHom_comp_tensorHom, h₁, h₂]

/-- **Invertibility of restricted Künneth maps**: under the hypotheses of
`map_kunnethNatTrans_app_comp_exchangeRight_app`, if the structure maps of `W` and `W'`, the
comparison morphisms and the exchange morphism of `β` are isomorphisms, and the Künneth map of
`F' ⊣ G'` at `M'` is an isomorphism, then so is `W` of the Künneth map of `F ⊣ G` at `M`. -/
lemma isIso_map_kunnethNatTrans_app
    (hβ : ∀ A B : D, β.hom.app (A ⊗ B) ≫ W'.map (δ F A B) ≫ δ W' (F.obj A) (F.obj B) =
      F'.map (δ W A B) ≫ δ F' (W.obj A) (W.obj B) ≫ (β.hom.app A ⊗ₘ β.hom.app B))
    {M : 𝒳} {M' : 𝒳'} (a₁ : W.obj (P.obj M) ⟶ P'.obj M') (a₂ : W.obj C₀ ⟶ C₀')
    (b₁ : W'.obj (Q.obj M) ⟶ Q'.obj M') (b₂ : W'.obj D₀ ⟶ D₀') [IsIso a₁] [IsIso a₂] [IsIso b₁]
    [IsIso b₂] [IsIso (δ W (P.obj M) C₀)] [IsIso (δ W' (Q.obj M) D₀)]
    (h₁ : β.hom.app (P.obj M) ≫ W'.map (e.hom.app M) ≫ b₁ = F'.map a₁ ≫ e'.hom.app M')
    (h₂ : β.hom.app C₀ ≫ W'.map c ≫ b₂ = F'.map a₂ ≫ c')
    (hex : IsIso ((exchangeRight adj adj' β).app (Q.obj M ⊗ D₀)))
    (h : IsIso ((adj'.kunnethNatTrans e' c').app M')) :
    IsIso (W.map ((adj.kunnethNatTrans e c).app M)) := by
  have hk := map_kunnethNatTrans_app_comp_exchangeRight_app adj adj' β e c e' c' hβ a₁ a₂ b₁ b₂
    h₁ h₂
  have hk' : IsIso ((δ W _ _ ≫ (a₁ ⊗ₘ a₂)) ≫ (adj'.kunnethNatTrans e' c').app M') :=
    inferInstance
  rw [← hk] at hk'
  have : IsIso ((exchangeRight adj adj' β).app ((Q ⋙ (curriedTensor C).flip.obj D₀).obj M)) :=
    hex
  exact IsIso.of_isIso_comp_right _
    ((exchangeRight adj adj' β).app _ ≫ G'.map (δ W' _ _ ≫ (b₁ ⊗ₘ b₂)))

/-- `isIso_map_kunnethNatTrans_app` with the comparison `b₁` of the first factors constructed
from an isomorphism `a₁` through `e`, `β` and `e'`. -/
lemma isIso_map_kunnethNatTrans_app_of_iso
    (hβ : ∀ A B : D, β.hom.app (A ⊗ B) ≫ W'.map (δ F A B) ≫ δ W' (F.obj A) (F.obj B) =
      F'.map (δ W A B) ≫ δ F' (W.obj A) (W.obj B) ≫ (β.hom.app A ⊗ₘ β.hom.app B))
    {M : 𝒳} {M' : 𝒳'} (a₁ : W.obj (P.obj M) ≅ P'.obj M') (a₂ : W.obj C₀ ⟶ C₀')
    (b₂ : W'.obj D₀ ⟶ D₀') [IsIso a₂] [IsIso b₂] [IsIso (δ W (P.obj M) C₀)]
    [IsIso (δ W' (Q.obj M) D₀)] (h₂ : β.hom.app C₀ ≫ W'.map c ≫ b₂ = F'.map a₂ ≫ c')
    (hex : IsIso ((exchangeRight adj adj' β).app (Q.obj M ⊗ D₀)))
    (h : IsIso ((adj'.kunnethNatTrans e' c').app M')) :
    IsIso (W.map ((adj.kunnethNatTrans e c).app M)) :=
  isIso_map_kunnethNatTrans_app adj adj' β e c e' c' hβ a₁.hom a₂
    (W'.map (e.inv.app M) ≫ β.inv.app (P.obj M) ≫ F'.map a₁.hom ≫ e'.hom.app M') b₂
    (by simp [← W'.map_comp_assoc]) h₂ hex h

omit [F.OplaxMonoidal] [W.OplaxMonoidal] [W'.OplaxMonoidal] in
/-- Precomposing the second factor `c'` of a Künneth map with `F' w` precomposes the Künneth map
with `P' M ◁ w`. -/
lemma kunnethNatTrans_app_map_comp {C₁ : D'} (w : C₁ ⟶ C₀') (M' : 𝒳') :
    (adj'.kunnethNatTrans e' (F'.map w ≫ c')).app M' =
      (P'.obj M' ◁ w) ≫ (adj'.kunnethNatTrans e' c').app M' := by
  rw [kunnethNatTrans_app, kunnethNatTrans_app, ← homEquiv_naturality_left,
    ← δ_natural_right_assoc]
  congr 2
  rw [← whiskerLeft_comp_tensorHom]

/-- **Invertibility of restricted Künneth maps, by comparison of transposes**: if `β` is
compatible with the oplax structure maps, the structure maps of `W` and `W'` and the exchange
morphism of `β` are isomorphisms, the transposes `C₀ ⟶ G D₀` and `C₀' ⟶ G' D₀'` of the second
factors `c` and `c'` are isomorphisms and the Künneth map of `F' ⊣ G'` at `M'` is an isomorphism,
then so is `W` of the Künneth map of `F ⊣ G` at `M`, for any isomorphisms `a₁`, `a₂`, `b₂`
comparing the ingredients. Indeed, through `a₂`, `β` and `b₂` the restriction of `c` is a second
factor `c''` for `F' ⊣ G'` whose transpose is an isomorphism, so that `c'' = F' w ≫ c'` for an
isomorphism `w`. -/
lemma isIso_map_kunnethNatTrans_app_of_isIso_homEquiv
    (hβ : ∀ A B : D, β.hom.app (A ⊗ B) ≫ W'.map (δ F A B) ≫ δ W' (F.obj A) (F.obj B) =
      F'.map (δ W A B) ≫ δ F' (W.obj A) (W.obj B) ≫ (β.hom.app A ⊗ₘ β.hom.app B))
    {M : 𝒳} {M' : 𝒳'} (a₁ : W.obj (P.obj M) ≅ P'.obj M') (a₂ : W.obj C₀ ≅ C₀')
    (b₂ : W'.obj D₀ ≅ D₀') [IsIso (δ W (P.obj M) C₀)] [IsIso (δ W' (Q.obj M) D₀)]
    (hex : IsIso ((exchangeRight adj adj' β).app (Q.obj M ⊗ D₀)))
    (hex₀ : IsIso ((exchangeRight adj adj' β).app D₀))
    (hc : IsIso (adj.homEquiv _ _ c)) (hc' : IsIso (adj'.homEquiv _ _ c'))
    (h : IsIso ((adj'.kunnethNatTrans e' c').app M')) :
    IsIso (W.map ((adj.kunnethNatTrans e c).app M)) := by
  have ht : adj'.homEquiv _ _ (F'.map a₂.inv ≫ β.hom.app C₀ ≫ W'.map c ≫ b₂.hom) =
      a₂.inv ≫ W.map (adj.homEquiv _ _ c) ≫ (exchangeRight adj adj' β).app D₀ ≫
        G'.map b₂.hom := by
    rw [homEquiv_naturality_left, ← Category.assoc, homEquiv_naturality_right,
      ← homEquiv_symm_map_homEquiv_comp_exchangeRight_app adj adj' β c, Equiv.apply_symm_apply]
    simp only [Category.assoc]
  have hti : IsIso (adj'.homEquiv _ _ (F'.map a₂.inv ≫ β.hom.app C₀ ≫ W'.map c ≫ b₂.hom)) := by
    rw [ht]
    infer_instance
  have hw : F'.map a₂.inv ≫ β.hom.app C₀ ≫ W'.map c ≫ b₂.hom =
      F'.map (adj'.homEquiv _ _ (F'.map a₂.inv ≫ β.hom.app C₀ ≫ W'.map c ≫ b₂.hom) ≫
        inv (adj'.homEquiv _ _ c')) ≫ c' := by
    apply (adj'.homEquiv _ _).injective
    conv_rhs => rw [homEquiv_naturality_left]
    rw [Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  refine isIso_map_kunnethNatTrans_app_of_iso adj adj' β e c e'
    (F'.map a₂.inv ≫ β.hom.app C₀ ≫ W'.map c ≫ b₂.hom) hβ a₁ a₂.hom b₂.hom
    (by simp [← F'.map_comp_assoc]) hex ?_
  rw [hw, kunnethNatTrans_app_map_comp]
  infer_instance

end CategoryTheory.Adjunction
