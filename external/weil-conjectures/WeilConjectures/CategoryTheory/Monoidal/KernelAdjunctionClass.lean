/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionBaseChange

/-!
# Kernels given by a class, and the left projection map

Inputs of the abstract kernel adjunction `CategoryTheory.Adjunction.kernelAdjunction`.

* Let `Δ ⊣ Δ'` be an adjunction with `Δ : E ⥤ D` strong monoidal (`Δ^* ⊣ Δ_*` for the diagonal
  `Δ : P ⟶ W`), such that the projection maps `Δ' 𝟙 ⊗ Y ⟶ Δ' (𝟙 ⊗ Δ Y)` are invertible. A *class*
  `c : Δ' 𝟙 ⟶ K` (the Gysin map `Δ_* Λ_P ⟶ Λ_W(1)[2]` of the diagonal) gives a *kernel*
  `κ_Y : Δ' Δ Y ≅ Δ' (𝟙 ⊗ Δ Y) ≅ Δ' 𝟙 ⊗ Y ⟶ K ⊗ Y`
  (`CategoryTheory.Adjunction.kernelOfClass`), which is linear for the projection maps
  (`CategoryTheory.Adjunction.kernelOfClass_linear`, the hypothesis `hκ` of
  `CategoryTheory.Adjunction.kernelAdjunction`), with associated class
  `𝟙 ⟶ Δ' Δ 𝟙 ⟶ Δ' 𝟙 ⟶ K` (`CategoryTheory.Adjunction.unit_app_comp_kernelOfClass_app`,
  the hypothesis `hδ`).
* For a braided left adjoint, the left projection map is the projection map up to braidings
  (`CategoryTheory.Adjunction.monoidalProjectionLeft_eq`), hence invertible as soon as the
  projection map is.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

section Unit

variable {D E : Type*} [Category* D] [Category* E] [MonoidalCategory D] [MonoidalCategory E]
  {Δ : E ⥤ D} {Δ' : D ⥤ E} (adjΔ : Δ ⊣ Δ') {K : E}

omit [MonoidalCategory D] in
/-- The class `𝟙 ⟶ K` associated with a natural transformation `κ : Δ' Δ Y ⟶ K ⊗ Y`: for every
`e : Y ⟶ 𝟙`, `Y ⟶ Δ' Δ Y ⟶ K ⊗ Y ⟶ K ⊗ 𝟙 ≅ K` is `e` followed by the class. -/
@[reassoc]
lemma unit_app_comp_app_whiskerLeft_rightUnitor (κ : Δ ⋙ Δ' ⟶ tensorLeft K) {Y : E}
    (e : Y ⟶ 𝟙_ E) :
    adjΔ.unit.app Y ≫ κ.app Y ≫ K ◁ e ≫ (ρ_ K).hom =
      e ≫ adjΔ.unit.app (𝟙_ E) ≫ κ.app (𝟙_ E) ≫ (ρ_ K).hom := by
  have h := κ.naturality e
  dsimp at h
  rw [← reassoc_of% h]
  exact adjΔ.unit_naturality_assoc e _

end Unit

section Class

variable {D E : Type*} [Category* D] [Category* E] [MonoidalCategory D] [MonoidalCategory E]
  {Δ : E ⥤ D} [Δ.Monoidal] {Δ' : D ⥤ E} (adjΔ : Δ ⊣ Δ') {K : E} (c : Δ'.obj (𝟙_ D) ⟶ K)
  [∀ Y, IsIso (adjΔ.monoidalProjection (𝟙_ D) Y)]

/-- The *kernel of a class* `c : Δ' 𝟙 ⟶ K`:
`κ_Y : Δ' Δ Y ≅ Δ' (𝟙 ⊗ Δ Y) ≅ Δ' 𝟙 ⊗ Y ⟶ K ⊗ Y`, the inverse of the projection map followed by
`c`. -/
@[simps]
noncomputable def kernelOfClass : Δ ⋙ Δ' ⟶ tensorLeft K where
  app Y := Δ'.map (λ_ (Δ.obj Y)).inv ≫ inv (adjΔ.monoidalProjection (𝟙_ D) Y) ≫ c ▷ Y
  naturality Y Y' g := by
    dsimp
    have h : Δ'.map (𝟙_ D ◁ Δ.map g) ≫ inv (adjΔ.monoidalProjection (𝟙_ D) Y') =
        inv (adjΔ.monoidalProjection (𝟙_ D) Y) ≫ Δ'.obj (𝟙_ D) ◁ g := by
      rw [IsIso.comp_inv_eq, assoc, adjΔ.monoidalProjection_naturality_right,
        IsIso.inv_hom_id_assoc]
    rw [← Δ'.map_comp_assoc, leftUnitor_inv_naturality, Δ'.map_comp_assoc, reassoc_of% h,
      whisker_exchange, assoc, assoc]

/-- **Linearity of the kernel of a class** for the projection maps of `Δ ⊣ Δ'`: the hypothesis
`hκ` of `CategoryTheory.Adjunction.kernelAdjunction`. -/
lemma kernelOfClass_linear (Y Z : E) :
    adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ (kernelOfClass adjΔ c).app (Y ⊗ Z) =
      (kernelOfClass adjΔ c).app Y ▷ Z ≫ (α_ _ _ _).hom := by
  have hα : adjΔ.monoidalProjection (𝟙_ D ⊗ Δ.obj Y) Z ≫ Δ'.map (α_ _ _ _).hom ≫
      Δ'.map (𝟙_ D ◁ μ Δ Y Z) ≫ inv (adjΔ.monoidalProjection (𝟙_ D) (Y ⊗ Z)) =
        inv (adjΔ.monoidalProjection (𝟙_ D) Y) ▷ Z ≫ (α_ _ _ _).hom := by
    rw [← Δ'.map_comp_assoc, ← cancel_epi (adjΔ.monoidalProjection (𝟙_ D) Y ▷ Z),
      adjΔ.monoidalProjection_assoc_assoc]
    simp
  have hl : μ Δ Y Z ≫ (λ_ (Δ.obj (Y ⊗ Z))).inv =
      (λ_ (Δ.obj Y)).inv ▷ Δ.obj Z ≫ (α_ _ _ _).hom ≫ 𝟙_ D ◁ μ Δ Y Z := by
    rw [leftUnitor_inv_naturality, leftUnitor_tensor_inv_assoc]
  simp only [kernelOfClass_app, comp_whiskerRight, assoc]
  rw [← Δ'.map_comp_assoc, hl, Δ'.map_comp, Δ'.map_comp, assoc, assoc,
    ← adjΔ.monoidalProjection_naturality_left_assoc, reassoc_of% hα,
    associator_naturality_left]

/-- The kernel of a class `c` at `𝟙` is `Δ' Δ 𝟙 ⟶ Δ' 𝟙` followed by `c`. -/
@[reassoc]
lemma kernelOfClass_app_tensorUnit :
    (kernelOfClass adjΔ c).app (𝟙_ E) ≫ (ρ_ K).hom = Δ'.map (η Δ) ≫ c := by
  have h := adjΔ.monoidalProjection_tensorUnit (𝟙_ D)
  rw [← IsIso.eq_inv_comp] at h
  rw [kernelOfClass_app, assoc, assoc, rightUnitor_naturality, ← reassoc_of% h,
    ← Δ'.map_comp_assoc, ← leftUnitor_inv_naturality_assoc, unitors_inv_equal, Iso.inv_hom_id,
    comp_id]

/-- The class associated with the kernel of a class `c` (the hypothesis `hδ` of
`CategoryTheory.Adjunction.kernelAdjunction`): for every `e : Y ⟶ 𝟙`,
`Y ⟶ Δ' Δ Y ⟶ K ⊗ Y ⟶ K ⊗ 𝟙 ≅ K` is `e` followed by `𝟙 ⟶ Δ' Δ 𝟙 ⟶ Δ' 𝟙 ⟶ K`. -/
lemma unit_app_comp_kernelOfClass_app {Y : E} (e : Y ⟶ 𝟙_ E) :
    adjΔ.unit.app Y ≫ (kernelOfClass adjΔ c).app Y ≫ K ◁ e ≫ (ρ_ K).hom =
      e ≫ adjΔ.unit.app (𝟙_ E) ≫ Δ'.map (η Δ) ≫ c := by
  rw [unit_app_comp_app_whiskerLeft_rightUnitor, kernelOfClass_app_tensorUnit]

end Class

section Braided

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] {F : C ⥤ D} [F.Braided] {G : D ⥤ C} (adj : F ⊣ G)

/-- For a braided left adjoint, the left projection map `N ⊗ G M ⟶ G (F N ⊗ M)` is the projection
map `G M ⊗ N ⟶ G (M ⊗ F N)` up to braidings. -/
lemma monoidalProjectionLeft_eq (N : C) (M : D) :
    adj.monoidalProjectionLeft N M =
      (β_ N (G.obj M)).hom ≫ adj.monoidalProjection M N ≫ G.map (β_ (F.obj N) M).inv := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    map_monoidalProjectionLeft_counit, Functor.id_obj]
  rw [map_monoidalProjection_counit_assoc, Functor.map_braiding, assoc, assoc,
    Functor.Monoidal.μ_δ_assoc, ← braiding_naturality_right_assoc, Iso.hom_inv_id, comp_id]

instance isIso_monoidalProjectionLeft (N : C) (M : D) [IsIso (adj.monoidalProjection M N)] :
    IsIso (adj.monoidalProjectionLeft N M) := by
  rw [monoidalProjectionLeft_eq]
  infer_instance

end Braided

section Composite

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] {H : C ⥤ E} [H.Monoidal]

/-- **Comparing two factorizations of a monoidal functor, on the inside.** Let
`cA : H ≅ F ⋙ A` and `cB : H ≅ F ⋙ B` be isomorphisms compatible with the comonoidal structures
(for derived pullbacks, the composition isomorphisms `L(qa)^* ≅ La^* Lq^*` and
`L(qb)^* ≅ Lb^* Lq^*` when `qa = qb`). Then `cA⁻¹ ≫ cB : F ⋙ A ≅ F ⋙ B` satisfies the hypothesis
`he` of `CategoryTheory.Adjunction.kernelAdjunction`. -/
lemma map_μ_comp_trans_hom_app {F : C ⥤ D} [F.Monoidal] {A B : D ⥤ E} [A.Monoidal]
    [B.Monoidal] (cA : H ≅ F ⋙ A) (cB : H ≅ F ⋙ B)
    (hA : ∀ X Y : C, δ H X Y ≫ (cA.hom.app X ⊗ₘ cA.hom.app Y) =
      cA.hom.app (X ⊗ Y) ≫ A.map (δ F X Y) ≫ δ A _ _)
    (hB : ∀ X Y : C, δ H X Y ≫ (cB.hom.app X ⊗ₘ cB.hom.app Y) =
      cB.hom.app (X ⊗ Y) ≫ B.map (δ F X Y) ≫ δ B _ _) (Y X : C) :
    A.map (μ F Y X) ≫ (cA.symm ≪≫ cB).hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ ((cA.symm ≪≫ cB).hom.app Y ⊗ₘ (cA.symm ≪≫ cB).hom.app X) ≫
        μ B (F.obj Y) (F.obj X) ≫ B.map (μ F Y X) := by
  have hA' : A.map (μ F Y X) ≫ cA.inv.app (Y ⊗ X) ≫ δ H Y X =
      δ A _ _ ≫ (cA.inv.app Y ⊗ₘ cA.inv.app X) := by
    rw [← cancel_mono (cA.hom.app Y ⊗ₘ cA.hom.app X), assoc, assoc, hA,
      Iso.inv_hom_id_app_assoc, ← A.map_comp_assoc, Functor.Monoidal.μ_δ, A.map_id, id_comp,
      assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  have hB' : cB.hom.app (Y ⊗ X) =
      δ H Y X ≫ (cB.hom.app Y ⊗ₘ cB.hom.app X) ≫ μ B _ _ ≫ B.map (μ F Y X) := by
    rw [reassoc_of% (hB Y X)]
    simp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [hB', reassoc_of% hA', tensorHom_comp_tensorHom_assoc]

/-- The unit version of `CategoryTheory.Adjunction.map_μ_comp_trans_hom_app`: the hypothesis
`he₀` of `CategoryTheory.Adjunction.kernelAdjunction`. -/
lemma trans_hom_app_tensorUnit_comp_η {F : C ⥤ D} [F.Monoidal] {A B : D ⥤ E} [A.Monoidal]
    [B.Monoidal] (cA : H ≅ F ⋙ A) (cB : H ≅ F ⋙ B)
    (hA : cA.hom.app (𝟙_ C) ≫ A.map (η F) ≫ η A = η H)
    (hB : cB.hom.app (𝟙_ C) ≫ B.map (η F) ≫ η B = η H) :
    (cA.symm ≪≫ cB).hom.app (𝟙_ C) ≫ B.map (η F) ≫ η B = A.map (η F) ≫ η A := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, assoc]
  rw [hB, ← hA, Iso.inv_hom_id_app_assoc]

/-- **Comparing two factorizations of a monoidal functor, on the outside.** Let
`cA : H ≅ A ⋙ Δ` and `cB : H ≅ B ⋙ Δ` be isomorphisms compatible with the comonoidal structures
(for derived pullbacks, `L(aΔ)^* ≅ LΔ^* La^*` and `L(bΔ)^* ≅ LΔ^* Lb^*` when `aΔ = bΔ`). Then
`cA⁻¹ ≫ cB : A ⋙ Δ ≅ B ⋙ Δ` satisfies the hypothesis `hι` of
`CategoryTheory.Adjunction.kernelAdjunction`. -/
lemma trans_hom_app_tensor {A B : C ⥤ D} [A.Monoidal] [B.Monoidal] {Δ : D ⥤ E} [Δ.Monoidal]
    (cA : H ≅ A ⋙ Δ) (cB : H ≅ B ⋙ Δ)
    (hA : ∀ X Y : C, δ H X Y ≫ (cA.hom.app X ⊗ₘ cA.hom.app Y) =
      cA.hom.app (X ⊗ Y) ≫ Δ.map (δ A X Y) ≫ δ Δ _ _)
    (hB : ∀ X Y : C, δ H X Y ≫ (cB.hom.app X ⊗ₘ cB.hom.app Y) =
      cB.hom.app (X ⊗ Y) ≫ Δ.map (δ B X Y) ≫ δ Δ _ _) (X Y : C) :
    (cA.symm ≪≫ cB).hom.app (X ⊗ Y) =
      Δ.map (δ A X Y) ≫ δ Δ _ _ ≫ ((cA.symm ≪≫ cB).hom.app X ⊗ₘ (cA.symm ≪≫ cB).hom.app Y) ≫
        μ Δ _ _ ≫ Δ.map (μ B X Y) := by
  have hA' : cA.inv.app (X ⊗ Y) ≫ δ H X Y =
      Δ.map (δ A X Y) ≫ δ Δ _ _ ≫ (cA.inv.app X ⊗ₘ cA.inv.app Y) := by
    rw [← cancel_mono (cA.hom.app X ⊗ₘ cA.hom.app Y), assoc, hA, Iso.inv_hom_id_app_assoc,
      assoc, assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  have hB' : cB.hom.app (X ⊗ Y) =
      δ H X Y ≫ (cB.hom.app X ⊗ₘ cB.hom.app Y) ≫ μ Δ _ _ ≫ Δ.map (μ B X Y) := by
    rw [reassoc_of% (hB X Y)]
    simp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [hB', reassoc_of% hA', tensorHom_comp_tensorHom_assoc]

end Composite

section Mate

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)
  {A : D ⥤ E} [A.Monoidal] {A' : E ⥤ D} (adjA : A ⊣ A') {B : D ⥤ E} [B.Monoidal]
  (e : F ⋙ A ≅ F ⋙ B)

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
/-- The base change map `F G M ⟶ A' B M` of `CategoryTheory.Adjunction.kernelBaseChange` is the
mate of `e` (for derived pullbacks and pushforwards, the derived base change map). -/
lemma kernelBaseChange_eq_mateEquiv_app (M : D) :
    kernelBaseChange adj adjA e M =
      (CategoryTheory.mateEquiv adj adjA (TwoSquare.mk _ _ _ _ e.hom)).app M := by
  apply (adjA.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, map_kernelBaseChange_counit,
    CategoryTheory.mateEquiv_counit]

end Mate

end CategoryTheory.Adjunction
