/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunction

/-!
# The unit given by a kernel

We continue `WeilConjectures.CategoryTheory.Monoidal.KernelAdjunction`. Let `F ⊣ G` be an
adjunction with `F : C ⥤ D` strong monoidal (`q^* ⊣ q_*` for `q : P ⟶ S`), and let `E` be a
third monoidal category (sheaves on `W = P ×_S P`) with strong monoidal functors
`A, B : D ⥤ E` (the pullbacks along the two projections `a, b : W ⟶ P`), an adjunction
`A ⊣ A'` (`a^* ⊣ a_*`) and an isomorphism `e : F ⋙ A ≅ F ⋙ B` (from `q a = q b`). Let further
`Δ : E ⥤ D` be strong monoidal with right adjoint `Δ'` (`Δ^* ⊣ Δ_*` for the diagonal), with an
isomorphism `ι : A ⋙ Δ ≅ B ⋙ Δ` (both are the identity, as `a Δ = b Δ = 1`).

* The *base change map* `β_M : F G M ⟶ A' B M` (`q^* q_* ⟶ a_* b^*`) is the mate of `e`
  (`CategoryTheory.Adjunction.kernelBaseChange`), and, for `T : D`, the comparison
  `Φ_M : T ⊗ F G M ⟶ T ⊗ A' B M ⟶ A' (A T ⊗ B M)` is `β` followed by the projection map of `A`
  (`CategoryTheory.Adjunction.kernelComparison`).
* For a *kernel* `κ : Δ' Δ Y ⟶ K ⊗ Y`, natural in `Y : E` (the action of
  `δ : Δ_* 1 ⟶ K`), the *kernel unit*
  `ψ_M : M ⟶ A' Δ' Δ A M ≅ A' Δ' Δ B M ⟶ A' (K ⊗ B M)`
  (`CategoryTheory.Adjunction.kernelUnit`) is the map `M = a_* Δ_* M ⟶ a_*(K ⊗ b^* M)` of
  blueprint `proposition-adjunction-projective-line` (G6).

When `Φ` is invertible, `u = Φ⁻¹ ∘ ψ : M ⟶ T ⊗ F G M` (with `K = A T`) is linear in the sense of
`CategoryTheory.Adjunction.ofTraceCounit`
(`CategoryTheory.Adjunction.kernelUnit_comp_inv_kernelComparison_linear`), provided `κ` is
linear for the projection maps of `Δ` and `ι` is compatible with `e` and the monoidal structures.

## Main definitions
- `CategoryTheory.Adjunction.monoidalProjectionLeft`
- `CategoryTheory.Adjunction.kernelBaseChange`
- `CategoryTheory.Adjunction.kernelComparison`
- `CategoryTheory.Adjunction.kernelUnit`

## Main statements
- `CategoryTheory.Adjunction.kernelUnit_linear`
- `CategoryTheory.Adjunction.kernelComparison_linear`
- `CategoryTheory.Adjunction.kernelUnit_comp_inv_kernelComparison_linear`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

section General

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)

/-- The unit of `F ⊣ G` is linear: `X ⊗ Y ⟶ G F X ⊗ Y ⟶ G (F X ⊗ F Y) ≅ G F (X ⊗ Y)` is the
unit at `X ⊗ Y`. -/
@[reassoc]
lemma unit_whiskerRight_monoidalProjection (X Y : C) :
    adj.unit.app X ▷ Y ≫ adj.monoidalProjection (F.obj X) Y ≫ G.map (μ F X Y) =
      adj.unit.app (X ⊗ Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_monoidalProjection_counit_assoc,
    counit_naturality, Functor.id_obj, Functor.comp_obj, left_triangle_components]
  rw [← δ_natural_left_assoc, ← comp_whiskerRight_assoc, left_triangle_components,
    id_whiskerRight, id_comp, Functor.Monoidal.δ_μ]

/-- The *left projection map* `N ⊗ G M ⟶ G (F N ⊗ M)`: the adjoint transpose of
`F (N ⊗ G M) ≅ F N ⊗ F G M ⟶ F N ⊗ M`. -/
noncomputable def monoidalProjectionLeft (N : C) (M : D) : N ⊗ G.obj M ⟶ G.obj (F.obj N ⊗ M) :=
  adj.homEquiv _ _ (δ F N (G.obj M) ≫ F.obj N ◁ adj.counit.app M)

@[reassoc]
lemma map_monoidalProjectionLeft_counit (N : C) (M : D) :
    F.map (adj.monoidalProjectionLeft N M) ≫ adj.counit.app (F.obj N ⊗ M) =
      δ F N (G.obj M) ≫ F.obj N ◁ adj.counit.app M := by
  have h := (adj.homEquiv _ _).symm_apply_apply (δ F N (G.obj M) ≫ F.obj N ◁ adj.counit.app M)
  rw [homEquiv_counit] at h
  exact h

/-- Naturality of the left projection map in the second variable. -/
@[reassoc]
lemma monoidalProjectionLeft_naturality_right (N : C) {M M' : D} (f : M ⟶ M') :
    N ◁ G.map f ≫ adj.monoidalProjectionLeft N M' =
      adj.monoidalProjectionLeft N M ≫ G.map (F.obj N ◁ f) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_monoidalProjectionLeft_counit,
    counit_naturality]
  rw [← δ_natural_right_assoc, map_monoidalProjectionLeft_counit_assoc, ← whiskerLeft_comp,
    ← whiskerLeft_comp]
  simp

end General

section Kernel

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)
  {A : D ⥤ E} [A.Monoidal] {A' : E ⥤ D} (adjA : A ⊣ A') {B : D ⥤ E} [B.Monoidal]
  (e : F ⋙ A ≅ F ⋙ B)

/-- The *base change map* `β_M : F G M ⟶ A' B M` (`q^* q_* ⟶ a_* b^*`): the adjoint transpose of
`A F G M ≅ B F G M ⟶ B M`. -/
noncomputable def kernelBaseChange (M : D) : F.obj (G.obj M) ⟶ A'.obj (B.obj M) :=
  adjA.homEquiv _ _ (e.hom.app (G.obj M) ≫ B.map (adj.counit.app M))

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
@[reassoc]
lemma map_kernelBaseChange_counit (M : D) :
    A.map (kernelBaseChange adj adjA e M) ≫ adjA.counit.app (B.obj M) =
      e.hom.app (G.obj M) ≫ B.map (adj.counit.app M) := by
  have h := (adjA.homEquiv _ _).symm_apply_apply (e.hom.app (G.obj M) ≫ B.map (adj.counit.app M))
  rw [homEquiv_counit] at h
  exact h

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
@[reassoc]
lemma kernelBaseChange_naturality {M M' : D} (f : M ⟶ M') :
    F.map (G.map f) ≫ kernelBaseChange adj adjA e M' =
      kernelBaseChange adj adjA e M ≫ A'.map (B.map f) := by
  have h := e.hom.naturality (G.map f)
  dsimp at h
  rw [kernelBaseChange, kernelBaseChange, ← homEquiv_naturality_left,
    ← homEquiv_naturality_right, reassoc_of% h, assoc, ← B.map_comp, ← B.map_comp]
  simp

/-- The comparison `Φ_M : T ⊗ F G M ⟶ T ⊗ A' B M ⟶ A' (A T ⊗ B M)`: the base change map
followed by the left projection map of `A ⊣ A'`. -/
noncomputable def kernelComparison (T M : D) :
    T ⊗ F.obj (G.obj M) ⟶ A'.obj (A.obj T ⊗ B.obj M) :=
  T ◁ kernelBaseChange adj adjA e M ≫ adjA.monoidalProjectionLeft T (B.obj M)

omit [MonoidalCategory C] [F.Monoidal] [B.Monoidal] in
@[reassoc]
lemma kernelComparison_naturality (T : D) {M M' : D} (f : M ⟶ M') :
    T ◁ F.map (G.map f) ≫ kernelComparison adj adjA e T M' =
      kernelComparison adj adjA e T M ≫ A'.map (A.obj T ◁ B.map f) := by
  rw [kernelComparison, kernelComparison, ← whiskerLeft_comp_assoc, kernelBaseChange_naturality,
    whiskerLeft_comp_assoc, monoidalProjectionLeft_naturality_right, assoc]

omit [MonoidalCategory C] [F.Monoidal] [B.Monoidal] in
@[reassoc]
lemma map_kernelComparison_counit (T M : D) :
    A.map (kernelComparison adj adjA e T M) ≫ adjA.counit.app (A.obj T ⊗ B.obj M) =
      δ A T (F.obj (G.obj M)) ≫ A.obj T ◁ (e.hom.app (G.obj M) ≫ B.map (adj.counit.app M)) := by
  rw [kernelComparison, Functor.map_comp, assoc, map_monoidalProjectionLeft_counit,
    ← δ_natural_right_assoc, ← whiskerLeft_comp, map_kernelBaseChange_counit]

/-- **Linearity of the comparison `Φ`.** `Φ_{M ⊗ F X}` composed with
`(T ⊗ F G M) ⊗ F X ≅ T ⊗ F (G M ⊗ X) ⟶ T ⊗ F G (M ⊗ F X)` is `Φ_M ⊗ F X` followed by the
projection map of `A ⊣ A'` and `A F X ≅ B F X`, provided `e` is monoidal. -/
lemma kernelComparison_linear
    (he : ∀ Y X : C, A.map (μ F Y X) ≫ e.hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ (e.hom.app Y ⊗ₘ e.hom.app X) ≫ μ B (F.obj Y) (F.obj X) ≫
        B.map (μ F Y X))
    (T M : D) (X : C) :
    (α_ _ _ _).hom ≫ T ◁ (μ F (G.obj M) X ≫ F.map (adj.monoidalProjection M X)) ≫
        kernelComparison adj adjA e T (M ⊗ F.obj X) =
      kernelComparison adj adjA e T M ▷ F.obj X ≫
        adjA.monoidalProjection (A.obj T ⊗ B.obj M) (F.obj X) ≫
          A'.map ((α_ _ _ _).hom ≫ A.obj T ◁ (B.obj M ◁ e.hom.app X ≫ μ B M (F.obj X))) := by
  have hin : A.map (μ F (G.obj M) X ≫ F.map (adj.monoidalProjection M X)) ≫
      e.hom.app (G.obj (M ⊗ F.obj X)) ≫ B.map (adj.counit.app (M ⊗ F.obj X)) =
        δ A _ _ ≫ (e.hom.app (G.obj M) ⊗ₘ e.hom.app X) ≫ μ B _ _ ≫
          B.map (adj.counit.app M ▷ F.obj X) := by
    have hn := e.hom.naturality (adj.monoidalProjection M X)
    dsimp at hn
    rw [Functor.map_comp, assoc, reassoc_of% hn, ← B.map_comp, map_monoidalProjection_counit,
      reassoc_of% he, B.map_comp, Functor.Monoidal.μ_δ_map_assoc]
  apply (adjA.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality, counit_naturality_assoc]
  rw [map_kernelComparison_counit, map_monoidalProjection_counit_assoc, ← δ_natural_left_assoc,
    ← comp_whiskerRight_assoc, map_kernelComparison_counit, ← δ_natural_right_assoc,
    ← whiskerLeft_comp, hin]
  have hinner : (e.hom.app (G.obj M) ⊗ₘ e.hom.app X) ≫ μ B _ _ ≫
      B.map (adj.counit.app M ▷ F.obj X) =
        (e.hom.app (G.obj M) ≫ B.map (adj.counit.app M)) ▷ A.obj (F.obj X) ≫
          B.obj M ◁ e.hom.app X ≫ μ B M (F.obj X) := by
    rw [tensorHom_def, assoc, ← μ_natural_left, comp_whiskerRight, assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [whisker_exchange_assoc]
  rw [whiskerLeft_comp, ← Functor.OplaxMonoidal.associativity_assoc, hinner]
  simp only [comp_whiskerRight, whiskerLeft_comp, assoc]
  erw [associator_naturality_middle_assoc, associator_naturality_middle_assoc]

/-- A monoidal isomorphism `e : F ⋙ A ≅ F ⋙ B` (compatible with the multiplications) is
compatible with the comultiplications. -/
lemma inv_app_map_δ_δ
    (he : ∀ Y X : C, A.map (μ F Y X) ≫ e.hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ (e.hom.app Y ⊗ₘ e.hom.app X) ≫ μ B (F.obj Y) (F.obj X) ≫
        B.map (μ F Y X)) (X Y : C) :
    e.inv.app (X ⊗ Y) ≫ A.map (δ F X Y) ≫ δ A (F.obj X) (F.obj Y) =
      B.map (δ F X Y) ≫ δ B (F.obj X) (F.obj Y) ≫ (e.inv.app X ⊗ₘ e.inv.app Y) := by
  rw [← cancel_epi (e.hom.app (X ⊗ Y)), Iso.hom_inv_id_app_assoc, ← cancel_epi (A.map (μ F X Y)),
    ← A.map_comp_assoc, Functor.Monoidal.μ_δ, A.map_id, id_comp, reassoc_of% (he X Y),
    ← B.map_comp_assoc, Functor.Monoidal.μ_δ, B.map_id, id_comp,
    Functor.Monoidal.μ_δ_assoc]
  simp

variable {Δ : E ⥤ D} [Δ.Monoidal] {Δ' : D ⥤ E} (adjΔ : Δ ⊣ Δ') (ι : A ⋙ Δ ≅ B ⋙ Δ) (K : E)
  (κ : Δ ⋙ Δ' ⟶ tensorLeft K)

/-- The adjoint transpose `A M ⟶ Δ' Δ A M ≅ Δ' Δ B M ⟶ K ⊗ B M` of the kernel unit
`CategoryTheory.Adjunction.kernelUnit`. -/
noncomputable def kernelUnitTranspose (M : D) : A.obj M ⟶ K ⊗ B.obj M :=
  adjΔ.unit.app (A.obj M) ≫ Δ'.map (ι.hom.app M) ≫ κ.app (B.obj M)

omit [MonoidalCategory C] [MonoidalCategory D] [F.Monoidal] [A.Monoidal] [B.Monoidal]
  [Δ.Monoidal] in
@[reassoc]
lemma kernelUnitTranspose_naturality {M M' : D} (f : M ⟶ M') :
    A.map f ≫ kernelUnitTranspose adjΔ ι K κ M' =
      kernelUnitTranspose adjΔ ι K κ M ≫ K ◁ B.map f := by
  have h₁ := adjΔ.unit.naturality (A.map f)
  have h₂ := ι.hom.naturality f
  have h₃ := κ.naturality (B.map f)
  dsimp at h₁ h₂ h₃
  rw [kernelUnitTranspose, kernelUnitTranspose, reassoc_of% h₁, assoc, ← Δ'.map_comp_assoc, h₂,
    Δ'.map_comp_assoc, h₃]
  simp only [assoc]

omit [MonoidalCategory C] [F.Monoidal] in
lemma kernelUnitTranspose_linear
    (hι : ∀ (M : D) (X : C), ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κ.app (Y ⊗ Z) =
      κ.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (M : D) (X : C) :
    kernelUnitTranspose adjΔ ι K κ (M ⊗ F.obj X) =
      δ A M (F.obj X) ≫ kernelUnitTranspose adjΔ ι K κ M ▷ A.obj (F.obj X) ≫ (α_ _ _ _).hom ≫
        K ◁ (B.obj M ◁ e.hom.app X ≫ μ B M (F.obj X)) := by
  have h₁ : adjΔ.unit.app (A.obj (M ⊗ F.obj X)) = δ A M (F.obj X) ≫
      adjΔ.unit.app (A.obj M ⊗ A.obj (F.obj X)) ≫ Δ'.map (Δ.map (μ A M (F.obj X))) := by
    rw [← adjΔ.unit_naturality_assoc, ← Δ'.map_comp, ← Δ.map_comp, Functor.Monoidal.δ_μ,
      Δ.map_id, Δ'.map_id, comp_id]
  have hn := κ.naturality (μ B M (F.obj X))
  dsimp at hn
  rw [kernelUnitTranspose, kernelUnitTranspose, h₁, hι, ← unit_whiskerRight_monoidalProjection]
  simp only [assoc]
  rw [← Δ'.map_comp_assoc, ← Δ'.map_comp_assoc]
  simp only [assoc, Functor.Monoidal.μ_δ_map_assoc, Functor.Monoidal.μ_δ_assoc]
  dsimp only [Functor.comp_obj]
  simp only [Δ'.map_comp, assoc]
  rw [hn, tensorHom_def, Δ'.map_comp, assoc,
    ← monoidalProjection_naturality_left_assoc, ← monoidalProjection_naturality_right_assoc,
    reassoc_of% hκ]
  erw [whisker_exchange_assoc, associator_naturality_right_assoc]
  simp only [comp_whiskerRight, whiskerLeft_comp, assoc]

/-- The *kernel unit* `ψ_M : M ⟶ A' Δ' Δ A M ≅ A' Δ' Δ B M ⟶ A' (K ⊗ B M)`: the adjoint transpose
of `CategoryTheory.Adjunction.kernelUnitTranspose` (for `a^* ⊣ a_*`, the map
`M = a_* Δ_* M ⟶ a_*(K ⊗ b^* M)` given by the kernel). -/
noncomputable def kernelUnit (M : D) : M ⟶ A'.obj (K ⊗ B.obj M) :=
  adjA.homEquiv _ _ (kernelUnitTranspose adjΔ ι K κ M)

omit [MonoidalCategory C] [MonoidalCategory D] [F.Monoidal] [A.Monoidal] [B.Monoidal]
  [Δ.Monoidal] in
@[reassoc]
lemma map_kernelUnit_counit (M : D) :
    A.map (kernelUnit adjA adjΔ ι K κ M) ≫ adjA.counit.app (K ⊗ B.obj M) =
      kernelUnitTranspose adjΔ ι K κ M := by
  have h := (adjA.homEquiv _ _).symm_apply_apply (kernelUnitTranspose adjΔ ι K κ M)
  rw [homEquiv_counit] at h
  exact h

omit [MonoidalCategory C] [MonoidalCategory D] [F.Monoidal] [A.Monoidal] [B.Monoidal]
  [Δ.Monoidal] in
@[reassoc]
lemma kernelUnit_naturality {M M' : D} (f : M ⟶ M') :
    f ≫ kernelUnit adjA adjΔ ι K κ M' =
      kernelUnit adjA adjΔ ι K κ M ≫ A'.map (K ◁ B.map f) := by
  rw [kernelUnit, kernelUnit, ← homEquiv_naturality_left, ← homEquiv_naturality_right,
    kernelUnitTranspose_naturality]

omit [MonoidalCategory C] [F.Monoidal] in
/-- **Linearity of the kernel unit.** -/
lemma kernelUnit_linear
    (hι : ∀ (M : D) (X : C), ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κ.app (Y ⊗ Z) =
      κ.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (M : D) (X : C) :
    kernelUnit adjA adjΔ ι K κ (M ⊗ F.obj X) =
      kernelUnit adjA adjΔ ι K κ M ▷ F.obj X ≫ adjA.monoidalProjection (K ⊗ B.obj M) (F.obj X) ≫
        A'.map ((α_ _ _ _).hom ≫ K ◁ (B.obj M ◁ e.hom.app X ≫ μ B M (F.obj X))) := by
  apply (adjA.homEquiv _ _).symm.injective
  rw [kernelUnit, Equiv.symm_apply_apply, kernelUnitTranspose_linear e adjΔ ι K κ hι hκ]
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality, counit_naturality_assoc]
  rw [map_monoidalProjection_counit_assoc, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc,
    map_kernelUnit_counit]

omit [MonoidalCategory C] in
/-- The kernel unit at an object `F τ` pulled back from `C`: by linearity it is the kernel unit at
`𝟙_ D` (the class `𝟙 ⟶ A' K`) tensored with `F τ`, followed by the projection map and
`A F τ ≅ B F τ`. -/
lemma kernelUnit_obj
    (hι : ∀ (M : D) (X : C), ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κ.app (Y ⊗ Z) =
      κ.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (τ : C) :
    kernelUnit adjA adjΔ ι K κ (F.obj τ) =
      (λ_ _).inv ≫ (kernelUnit adjA adjΔ ι K κ (𝟙_ D) ≫ A'.map (K ◁ η B ≫ (ρ_ K).hom)) ▷
        F.obj τ ≫ adjA.monoidalProjection K (F.obj τ) ≫ A'.map (K ◁ e.hom.app τ) := by
  have hn := kernelUnit_naturality adjA adjΔ ι K κ (λ_ (F.obj τ)).hom
  rw [kernelUnit_linear (e := e) adjA adjΔ ι K κ hι hκ] at hn
  rw [← cancel_epi (λ_ (F.obj τ)).hom, hn, Iso.hom_inv_id_assoc, comp_whiskerRight]
  simp only [assoc]
  rw [monoidalProjection_naturality_left_assoc, ← A'.map_comp, ← A'.map_comp]
  congr 3
  rw [assoc, ← whiskerLeft_comp, assoc, Functor.Monoidal.map_leftUnitor,
    Functor.Monoidal.μ_δ_assoc]
  erw [whisker_exchange_assoc, leftUnitor_naturality]
  simp only [whiskerLeft_comp, comp_whiskerRight, assoc]
  rw [← associator_naturality_middle_assoc, triangle_assoc]

/-- The *trace along `a`*, `t_a : A' B T ≅ F G T ⟶ F 𝟙 ≅ 𝟙`: the base change of a trace
`t : G T ⟶ 𝟙` along the base change map `CategoryTheory.Adjunction.kernelBaseChange`
(for `a : P ×_S P ⟶ P`, the trace of the projective line `a` over `P`, by
`det-sp-p1-trace` (2)). -/
noncomputable def kernelTraceA (T : D) (t : G.obj T ⟶ 𝟙_ C)
    [IsIso (kernelBaseChange adj adjA e T)] : A'.obj (B.obj T) ⟶ 𝟙_ D :=
  inv (kernelBaseChange adj adjA e T) ≫ F.map t ≫ η F

variable (T : D) (κT : Δ ⋙ Δ' ⟶ tensorLeft (A.obj T))
  [∀ M, IsIso (kernelComparison adj adjA e T M)]

/-- The unit `u_M : M ⟶ A' (A T ⊗ B M) ≅ T ⊗ F G M` of the kernel `κ : Δ' Δ Y ⟶ A T ⊗ Y`: the
kernel unit `CategoryTheory.Adjunction.kernelUnit` followed by the inverse of the comparison
`CategoryTheory.Adjunction.kernelComparison`. -/
@[simps]
noncomputable def kernelAdjunctionUnit : 𝟭 D ⟶ G ⋙ F ⋙ tensorLeft T where
  app M := kernelUnit adjA adjΔ ι (A.obj T) κT M ≫ inv (kernelComparison adj adjA e T M)
  naturality M M' f := by
    dsimp
    rw [kernelUnit_naturality_assoc, assoc]
    congr 1
    rw [IsIso.eq_inv_comp, ← kernelComparison_naturality_assoc, IsIso.hom_inv_id, comp_id]

/-- **Linearity of the unit given by a kernel**, in the form required by
`CategoryTheory.Adjunction.ofTraceCounit`. -/
lemma kernelAdjunctionUnit_linear
    (he : ∀ Y X : C, A.map (μ F Y X) ≫ e.hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ (e.hom.app Y ⊗ₘ e.hom.app X) ≫ μ B (F.obj Y) (F.obj X) ≫
        B.map (μ F Y X))
    (hι : ∀ (M : D) (X : C), ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κT.app (Y ⊗ Z) =
      κT.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (M : D) (X : C) :
    (kernelAdjunctionUnit adj adjA e adjΔ ι T κT).app (M ⊗ F.obj X) =
      (kernelAdjunctionUnit adj adjA e adjΔ ι T κT).app M ▷ F.obj X ≫ (α_ _ _ _).hom ≫
        T ◁ (μ F (G.obj M) X ≫ F.map (adj.monoidalProjection M X)) := by
  simp only [kernelAdjunctionUnit_app]
  rw [← cancel_mono (kernelComparison adj adjA e T (M ⊗ F.obj X)), assoc, IsIso.inv_hom_id,
    comp_id, assoc, assoc, kernelComparison_linear adj adjA e he, ← comp_whiskerRight_assoc,
    assoc, IsIso.inv_hom_id, comp_id]
  exact kernelUnit_linear (e := e) adjA adjΔ ι _ κT hι hκ M X

end Kernel

end CategoryTheory.Adjunction
