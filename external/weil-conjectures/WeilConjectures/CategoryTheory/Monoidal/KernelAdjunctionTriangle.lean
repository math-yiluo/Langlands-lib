/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionBaseChange

/-!
# The adjunction given by a kernel

We continue `WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionUnit` and
`WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionBaseChange`, for an object `T = F τ`
pulled back from `C` (for `q : ℙ¹_S ⟶ S`, `τ = Λ_S(1)[2]`), and prove the abstract form of
blueprint `proposition-adjunction-projective-line` (G5)–(G9): the unit given by a kernel and the
trace counit are the unit and counit of an adjunction `G ⊣ T ⊗ F (-)` as soon as the two *integrals
of the diagonal class* are `1` (`CategoryTheory.Adjunction.kernelAdjunction`).

* The normalization at `T` (the second triangle identity, (G9)) follows from the integral along
  `a` of the class `𝟙 ⟶ A' (A T) ≅ A' (B T)`, against the trace `t_a : A' B T ≅ F G T ⟶ 𝟙`
  given by base change of `t` (`CategoryTheory.Adjunction.kernelAdjunctionUnit_app_comp_trace`).
  Here the factor `T` coming from the coefficient is exchanged with the factor `T` carrying the
  class: this uses that the braiding of `A T ⊗ A T` is the identity (for `Λ(1)[2]` the shift is
  even and the Tate twist is a line),
  `CategoryTheory.Adjunction.monoidalProjection_comp_map_whiskerLeft`.
* The normalization at `𝟙` (the first triangle identity, (G8)) follows from the integral along
  `b` (`CategoryTheory.Adjunction.map_kernelAdjunctionUnit_app_comp_traceCounit`).

## Main definitions
- `CategoryTheory.Adjunction.kernelAdjunction`

## Main statements
- `CategoryTheory.Adjunction.kernelAdjunction_counit`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory BraidedCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)
  {A : D ⥤ E} [A.Braided] {A' : E ⥤ D} (adjA : A ⊣ A') {B : D ⥤ E} [B.Monoidal]
  (e : F ⋙ A ≅ F ⋙ B)

omit [MonoidalCategory C] [F.Monoidal] [B.Monoidal] in
/-- **Exchange of the two factors.** If the braiding of `A F τ ⊗ A F τ` is the identity, the
right projection map `A' (A F τ) ⊗ F τ ⟶ A' (A F τ ⊗ A F τ) ≅ A' (A F τ ⊗ B F τ)` is the
braiding followed by the left projection map. -/
@[reassoc]
lemma monoidalProjection_comp_map_whiskerLeft (τ : C)
    (hsymm : (β_ (A.obj (F.obj τ)) (A.obj (F.obj τ))).hom = 𝟙 _) :
    adjA.monoidalProjection (A.obj (F.obj τ)) (F.obj τ) ≫
        A'.map (A.obj (F.obj τ) ◁ e.hom.app τ) =
      A'.map (e.hom.app τ) ▷ F.obj τ ≫ (β_ _ _).hom ≫
        adjA.monoidalProjectionLeft (F.obj τ) (B.obj (F.obj τ)) := by
  apply (adjA.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj]
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    map_monoidalProjection_counit_assoc, map_monoidalProjectionLeft_counit,
    Functor.map_braiding, Functor.Monoidal.μ_δ_assoc]
  rw [← δ_natural_left_assoc, braiding_naturality_left_assoc, ← whiskerLeft_comp]
  erw [adjA.counit_naturality]
  rw [whiskerLeft_comp, ← braiding_naturality_left_assoc, hsymm, id_comp]

variable {Δ : E ⥤ D} [Δ.Monoidal] {Δ' : D ⥤ E} (adjΔ : Δ ⊣ Δ') (ι : A ⋙ Δ ≅ B ⋙ Δ)

/-- **The second triangle identity from the integral along `a`.** For `T = F τ` with the braiding
of `A T ⊗ A T` trivial, the unit given by a linear kernel satisfies the normalization at `T` of
`CategoryTheory.Adjunction.ofTraceCounit` as soon as the class `𝟙 ⟶ A' (A T) ≅ A' (B T)` given by
the kernel has integral `1` against the trace `t_a` along `a`. -/
lemma kernelAdjunctionUnit_app_comp_trace (τ : C)
    (κT : Δ ⋙ Δ' ⟶ tensorLeft (A.obj (F.obj τ)))
    [∀ M, IsIso (kernelComparison adj adjA e (F.obj τ) M)] (t : G.obj (F.obj τ) ⟶ 𝟙_ C)
    [IsIso (kernelBaseChange adj adjA e (F.obj τ))]
    (hι : ∀ (M : D) (X : C), ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κT.app (Y ⊗ Z) =
      κT.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (hsymm : (β_ (A.obj (F.obj τ)) (A.obj (F.obj τ))).hom = 𝟙 _)
    (hint : kernelUnit adjA adjΔ ι _ κT (𝟙_ D) ≫
      A'.map (A.obj (F.obj τ) ◁ η B ≫ (ρ_ _).hom ≫ e.hom.app τ) ≫
        kernelTraceA adj adjA e (F.obj τ) t = 𝟙 _) :
    (kernelAdjunctionUnit adj adjA e adjΔ ι (F.obj τ) κT).app (F.obj τ) ≫
      F.obj τ ◁ (F.map t ≫ η F) ≫ (ρ_ _).hom = 𝟙 _ := by
  have hπ : adjA.monoidalProjectionLeft (F.obj τ) (B.obj (F.obj τ)) ≫
      inv (kernelComparison adj adjA e (F.obj τ) (F.obj τ)) =
        F.obj τ ◁ inv (kernelBaseChange adj adjA e (F.obj τ)) := by
    rw [IsIso.comp_inv_eq, kernelComparison, ← whiskerLeft_comp_assoc, IsIso.inv_hom_id,
      whiskerLeft_id, id_comp]
  simp only [kernelAdjunctionUnit_app, assoc]
  rw [kernelUnit_obj (e := e) adjA adjΔ ι _ κT hι hκ]
  simp only [assoc]
  rw [monoidalProjection_comp_map_whiskerLeft_assoc adjA e τ hsymm, reassoc_of% hπ,
    ← whiskerLeft_comp_assoc, ← braiding_naturality_left_assoc,
    braiding_rightUnitor, ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  simp only [Functor.map_comp, assoc, kernelTraceA] at hint ⊢
  rw [hint, id_whiskerRight, id_comp, Iso.inv_hom_id]

variable {B' : E ⥤ D} (adjB : B ⊣ B')

/-- **The adjunction given by a kernel** (blueprint `proposition-adjunction-projective-line`,
(G5)–(G9)).

Setting: `F ⊣ G` (`q^* ⊣ q_*` for `q : P ⟶ S`) with `F` strong monoidal; strong monoidal
`A, B : D ⥤ E` (`a^*, b^*` for the projections of `W = P ×_S P`) with right adjoints `A'`, `B'`,
`A` braided; a monoidal isomorphism `e : F ⋙ A ≅ F ⋙ B` (`q a = q b`, hypotheses `he`, `he₀`); a
strong monoidal `Δ : E ⥤ D` with right adjoint `Δ'` (the diagonal); a monoidal isomorphism
`ι : A ⋙ Δ ≅ B ⋙ Δ` (`a Δ = b Δ`, hypothesis `hι`) which is `Δ e` on objects pulled back from `C`
(hypothesis `hιF`); an object `T = F τ` (`Λ(1)[2]`) such that the braiding of `A T ⊗ A T` is
trivial (`hsymm`) and `F ⊣ G` satisfies the projection formula at `T`; the base change maps
`F G ⟶ A' B` (all objects) and `F G T ⟶ B' A T` and the left projection maps of `A ⊣ A'` are
invertible; a trace `t : G T ⟶ 𝟙`; a *kernel* `κ : Δ' Δ Y ⟶ A T ⊗ Y`, linear for the projection
maps of `Δ ⊣ Δ'` (`hκ`), with class `δ_W : 𝟙 ⟶ A T` (`hδ`).

If the two integrals of `δ_W` are `1` (`hintA`: along `a` against `t_a`, with `A T ≅ B T`;
`hintB`: along `b` against `t_b`), then `G` is left adjoint to `T ⊗ F (-)`, with counit the trace
counit `G (T ⊗ F N) ≅ G T ⊗ N ⟶ N` (`CategoryTheory.Adjunction.kernelAdjunction_counit`) and unit
`CategoryTheory.Adjunction.kernelAdjunctionUnit`. -/
noncomputable def kernelAdjunction (τ : C) (t : G.obj (F.obj τ) ⟶ 𝟙_ C)
    (κ : Δ ⋙ Δ' ⟶ tensorLeft (A.obj (F.obj τ))) (δW : 𝟙_ E ⟶ A.obj (F.obj τ))
    [∀ N, IsIso (adj.monoidalProjection (F.obj τ) N)]
    [∀ M, IsIso (kernelBaseChange adj adjA e M)]
    [∀ N Y, IsIso (adjA.monoidalProjectionLeft N Y)]
    [IsIso (kernelBaseChange adj adjB e.symm (F.obj τ))]
    (he : ∀ Y X : C, A.map (μ F Y X) ≫ e.hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ (e.hom.app Y ⊗ₘ e.hom.app X) ≫ μ B (F.obj Y) (F.obj X) ≫
        B.map (μ F Y X))
    (he₀ : e.hom.app (𝟙_ C) ≫ B.map (η F) ≫ η B = A.map (η F) ≫ η A)
    (hι : ∀ M M' : D, ι.hom.app (M ⊗ M') =
      Δ.map (δ A M M') ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ ι.hom.app M') ≫ μ Δ _ _ ≫ Δ.map (μ B M M'))
    (hιF : ∀ X : C, ι.hom.app (F.obj X) = Δ.map (e.hom.app X))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κ.app (Y ⊗ Z) =
      κ.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (hδ : adjΔ.unit.app (B.obj (𝟙_ D)) ≫ κ.app (B.obj (𝟙_ D)) ≫ A.obj (F.obj τ) ◁ η B ≫
      (ρ_ _).hom = η B ≫ δW)
    (hsymm : (β_ (A.obj (F.obj τ)) (A.obj (F.obj τ))).hom = 𝟙 _)
    (hintA : adjA.unit.app (𝟙_ D) ≫ A'.map (η A ≫ δW ≫ e.hom.app τ) ≫
      kernelTraceA adj adjA e (F.obj τ) t = 𝟙 _)
    (hintB : adjB.unit.app (𝟙_ D) ≫ B'.map (η B ≫ δW) ≫
      kernelTraceA adj adjB e.symm (F.obj τ) t = 𝟙 _) :
    G ⊣ F ⋙ tensorLeft (F.obj τ) := by
  haveI (M : D) : IsIso (kernelComparison adj adjA e (F.obj τ) M) := by
    rw [kernelComparison]
    infer_instance
  have hι' (M : D) (X : C) : ι.hom.app (M ⊗ F.obj X) =
      Δ.map (δ A M (F.obj X)) ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ Δ.map (e.hom.app X)) ≫ μ Δ _ _ ≫
        Δ.map (μ B M (F.obj X)) := by
    rw [hι, hιF]
    rfl
  have hι₁ : ι.hom.app (𝟙_ D) =
      Δ.map (A.map (ε F)) ≫ Δ.map (e.hom.app (𝟙_ C)) ≫ Δ.map (B.map (η F)) := by
    have h := ι.hom.naturality (ε F)
    dsimp at h
    rw [← hιF, reassoc_of% h, ← Δ.map_comp, ← B.map_comp, Functor.Monoidal.ε_η, B.map_id,
      Δ.map_id, comp_id]
  have hu₁ : adjΔ.unit.app (A.obj (𝟙_ D)) ≫ Δ'.map (ι.hom.app (𝟙_ D)) ≫
      κ.app (B.obj (𝟙_ D)) ≫ A.obj (F.obj τ) ◁ η B ≫ (ρ_ _).hom = η A ≫ δW := by
    rw [hι₁, Δ'.map_comp, Δ'.map_comp]
    simp only [assoc]
    erw [adjΔ.unit_naturality_assoc, adjΔ.unit_naturality_assoc, adjΔ.unit_naturality_assoc]
    rw [hδ]
    erw [reassoc_of% he₀]
    rw [Functor.Monoidal.ε_η_map_assoc]
  exact ofTraceCounit (kernelAdjunctionUnit adj adjA e adjΔ ι (F.obj τ) κ)
    (kernelAdjunctionUnit_linear adj adjA e adjΔ ι (F.obj τ) κ he hι' hκ)
    (map_kernelAdjunctionUnit_app_comp_traceCounit adj adjA adjB e adjΔ ι (F.obj τ) κ t
      (inv_app_map_δ_δ e he) hιF (by rw [hδ]; exact hintB))
    (kernelAdjunctionUnit_app_comp_trace adj adjA e adjΔ ι τ κ t hι' hκ hsymm (by
      rw [kernelUnit, homEquiv_unit, assoc, ← A'.map_comp_assoc, kernelUnitTranspose]
      simp only [assoc]
      rw [reassoc_of% hu₁]
      exact hintA))

@[simp]
lemma kernelAdjunction_counit (τ : C) (t : G.obj (F.obj τ) ⟶ 𝟙_ C)
    (κ : Δ ⋙ Δ' ⟶ tensorLeft (A.obj (F.obj τ))) (δW : 𝟙_ E ⟶ A.obj (F.obj τ))
    [∀ N, IsIso (adj.monoidalProjection (F.obj τ) N)]
    [∀ M, IsIso (kernelBaseChange adj adjA e M)]
    [∀ N Y, IsIso (adjA.monoidalProjectionLeft N Y)]
    [IsIso (kernelBaseChange adj adjB e.symm (F.obj τ))]
    (he : ∀ Y X : C, A.map (μ F Y X) ≫ e.hom.app (Y ⊗ X) =
      δ A (F.obj Y) (F.obj X) ≫ (e.hom.app Y ⊗ₘ e.hom.app X) ≫ μ B (F.obj Y) (F.obj X) ≫
        B.map (μ F Y X))
    (he₀ : e.hom.app (𝟙_ C) ≫ B.map (η F) ≫ η B = A.map (η F) ≫ η A)
    (hι : ∀ M M' : D, ι.hom.app (M ⊗ M') =
      Δ.map (δ A M M') ≫ δ Δ _ _ ≫ (ι.hom.app M ⊗ₘ ι.hom.app M') ≫ μ Δ _ _ ≫ Δ.map (μ B M M'))
    (hιF : ∀ X : C, ι.hom.app (F.obj X) = Δ.map (e.hom.app X))
    (hκ : ∀ Y Z : E, adjΔ.monoidalProjection (Δ.obj Y) Z ≫ Δ'.map (μ Δ Y Z) ≫ κ.app (Y ⊗ Z) =
      κ.app Y ▷ Z ≫ (α_ _ _ _).hom)
    (hδ : adjΔ.unit.app (B.obj (𝟙_ D)) ≫ κ.app (B.obj (𝟙_ D)) ≫ A.obj (F.obj τ) ◁ η B ≫
      (ρ_ _).hom = η B ≫ δW)
    (hsymm : (β_ (A.obj (F.obj τ)) (A.obj (F.obj τ))).hom = 𝟙 _)
    (hintA : adjA.unit.app (𝟙_ D) ≫ A'.map (η A ≫ δW ≫ e.hom.app τ) ≫
      kernelTraceA adj adjA e (F.obj τ) t = 𝟙 _)
    (hintB : adjB.unit.app (𝟙_ D) ≫ B'.map (η B ≫ δW) ≫
      kernelTraceA adj adjB e.symm (F.obj τ) t = 𝟙 _) :
    (kernelAdjunction adj adjA e adjΔ ι adjB τ t κ δW he he₀ hι hιF hκ hδ hsymm hintA
      hintB).counit = adj.traceCounit (F.obj τ) t :=
  rfl

end CategoryTheory.Adjunction
