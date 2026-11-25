/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionUnit

/-!
# The first triangle identity for the unit given by a kernel

We continue `WeilConjectures.CategoryTheory.Monoidal.KernelAdjunctionUnit`, now with a right
adjoint `B'` of `B` (`b^* ⊣ b_*`). The *comparison* `θ_Y : G A' Y ⟶ G B' Y`
(`q_* a_* ≅ (q a)_* = (q b)_* ≅ q_* b_*`, `CategoryTheory.Adjunction.kernelPushforwardComparison`)
is the adjoint transpose of `B F G A' Y ≅ A F G A' Y ⟶ A A' Y ⟶ Y`.

The normalization at `𝟙_ D` of `CategoryTheory.Adjunction.ofTraceCounit` (the first triangle
identity) for the unit given by a kernel follows from the integral along `b` of the class
`𝟙 ⟶ B' (A T)` given by the kernel, against the trace `t_b : B' A T ≅ F G T ⟶ F 𝟙 ≅ 𝟙` along `b`
(`CategoryTheory.Adjunction.map_kernelAdjunctionUnit_app_comp_traceCounit`). This is the argument
(G8) of blueprint `proposition-adjunction-projective-line`: after `q_*`, the projection formula for
`q` and the base change for `a` become the base change and the projection formula for `b`
(`CategoryTheory.Adjunction.monoidalProjectionLeft_comp_map_kernelBaseChange`), and the unit of
`a Δ = 1` becomes the unit of `b Δ = 1` (
`CategoryTheory.Adjunction.map_unit_comp_kernelPushforwardComparison`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

section General

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)

/-- Right unitality of the projection map. -/
@[reassoc]
lemma monoidalProjection_tensorUnit (M : D) :
    adj.monoidalProjection M (𝟙_ C) ≫ G.map (M ◁ η F ≫ (ρ_ M).hom) = (ρ_ (G.obj M)).hom := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    Functor.Monoidal.map_rightUnitor]
  erw [adj.counit_naturality_assoc]
  rw [map_monoidalProjection_counit_assoc]
  erw [← whisker_exchange_assoc, rightUnitor_naturality]

instance isIso_monoidalProjection_tensorUnit (M : D) :
    IsIso (adj.monoidalProjection M (𝟙_ C)) := by
  have h := adj.monoidalProjection_tensorUnit M
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

/-- A map `f : N ⟶ 𝟙` tensored with `G M` is computed by the left projection map. -/
lemma whiskerRight_leftUnitor_eq_monoidalProjectionLeft (N : C) (f : N ⟶ 𝟙_ C) (M : D) :
    f ▷ G.obj M ≫ (λ_ (G.obj M)).hom =
      adj.monoidalProjectionLeft N M ≫ G.map ((F.map f ≫ η F) ▷ M ≫ (λ_ M).hom) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    Functor.Monoidal.map_leftUnitor]
  erw [adj.counit_naturality_assoc]
  rw [map_monoidalProjectionLeft_counit_assoc, ← δ_natural_left_assoc, ← comp_whiskerRight_assoc]
  erw [whisker_exchange_assoc, leftUnitor_naturality]

end General

section Kernel

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [MonoidalCategory C]
  [MonoidalCategory D] [MonoidalCategory E]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G)
  {A : D ⥤ E} [A.Monoidal] {A' : E ⥤ D} (adjA : A ⊣ A')
  {B : D ⥤ E} [B.Monoidal] {B' : E ⥤ D} (adjB : B ⊣ B') (e : F ⋙ A ≅ F ⋙ B)

/-- The comparison `θ_Y : G A' Y ⟶ G B' Y` (`q_* a_* ≅ q_* b_*`): the adjoint transpose of
`B F G A' Y ≅ A F G A' Y ⟶ A A' Y ⟶ Y`. -/
noncomputable def kernelPushforwardComparison (Y : E) : G.obj (A'.obj Y) ⟶ G.obj (B'.obj Y) :=
  adj.homEquiv _ _
    (adjB.homEquiv _ _ (e.inv.app _ ≫ A.map (adj.counit.app _) ≫ adjA.counit.app Y))

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
@[reassoc]
lemma map_map_kernelPushforwardComparison_counit (Y : E) :
    B.map (F.map (kernelPushforwardComparison adj adjA adjB e Y)) ≫
        B.map (adj.counit.app (B'.obj Y)) ≫ adjB.counit.app Y =
      e.inv.app _ ≫ A.map (adj.counit.app _) ≫ adjA.counit.app Y := by
  have h₁ := (adj.homEquiv _ _).symm_apply_apply
    (adjB.homEquiv _ _ (e.inv.app _ ≫ A.map (adj.counit.app _) ≫ adjA.counit.app Y))
  have h₂ := (adjB.homEquiv _ _).symm_apply_apply
    (e.inv.app _ ≫ A.map (adj.counit.app _) ≫ adjA.counit.app Y)
  rw [homEquiv_counit] at h₁ h₂
  rw [← B.map_comp_assoc]
  exact (congrArg (fun φ ↦ B.map φ ≫ adjB.counit.app Y) h₁).trans h₂

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
@[reassoc]
lemma kernelPushforwardComparison_naturality {Y Y' : E} (f : Y ⟶ Y') :
    G.map (A'.map f) ≫ kernelPushforwardComparison adj adjA adjB e Y' =
      kernelPushforwardComparison adj adjA adjB e Y ≫ G.map (B'.map f) := by
  apply (adj.homEquiv _ _).symm.injective
  apply (adjB.homEquiv _ _).symm.injective
  have hn := e.inv.naturality (G.map (A'.map f))
  dsimp at hn
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    map_map_kernelPushforwardComparison_counit, map_map_kernelPushforwardComparison_counit_assoc]
  rw [reassoc_of% hn, ← A.map_comp_assoc]
  simp

/-- **Projection formula and base change** (blueprint `proposition-adjunction-projective-line`
(G8)). After `G`, the projection map of `F ⊣ G` followed by the comparison `Φ` and by `θ` is the
left projection map of `F ⊣ G` followed by the base change map `F G T ⟶ B' A T` and the projection
map of `B ⊣ B'`, provided `e` is monoidal. -/
lemma monoidalProjectionLeft_comp_map_kernelBaseChange
    (he' : ∀ X Y : C, e.inv.app (X ⊗ Y) ≫ A.map (δ F X Y) ≫ δ A (F.obj X) (F.obj Y) =
      B.map (δ F X Y) ≫ δ B (F.obj X) (F.obj Y) ≫ (e.inv.app X ⊗ₘ e.inv.app Y))
    (T M : D) :
    adj.monoidalProjectionLeft (G.obj T) M ≫
        G.map (kernelBaseChange adj adjB e.symm T ▷ M ≫ adjB.monoidalProjection (A.obj T) M) =
      adj.monoidalProjection T (G.obj M) ≫ G.map (kernelComparison adj adjA e T M) ≫
        kernelPushforwardComparison adj adjA adjB e (A.obj T ⊗ B.obj M) := by
  apply (adj.homEquiv _ _).symm.injective
  apply (adjB.homEquiv _ _).symm.injective
  have hn := e.inv.naturality (adj.monoidalProjection T (G.obj M) ≫
    G.map (kernelComparison adj adjA e T M))
  dsimp at hn
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    counit_naturality_assoc, map_map_kernelPushforwardComparison_counit]
  rw [← B.map_comp_assoc, map_monoidalProjectionLeft_counit, map_monoidalProjection_counit,
    ← δ_natural_left_assoc, ← comp_whiskerRight, map_kernelBaseChange_counit]
  simp only [Functor.map_comp, assoc] at hn
  rw [reassoc_of% hn, ← A.map_comp_assoc, ← A.map_comp_assoc, assoc]
  erw [adj.counit_naturality]
  rw [map_monoidalProjection_counit_assoc, A.map_comp, A.map_comp, assoc, assoc,
    map_kernelComparison_counit, ← δ_natural_left_assoc, reassoc_of% (he' (G.obj T) (G.obj M)),
    B.map_comp, assoc]
  erw [← δ_natural_right_assoc]
  congr 2
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp, assoc, Iso.symm_hom]
  erw [whisker_exchange_assoc (f := e.inv.app (G.obj T)) (g := B.map (adj.counit.app M)),
    whisker_exchange (f := A.map (adj.counit.app T)) (g := B.map (adj.counit.app M)),
    whisker_exchange_assoc (f := A.map (adj.counit.app T)) (g := e.inv.app (G.obj M))]
  erw [← whiskerLeft_comp_assoc, e.inv_hom_id_app]
  simp

variable {Δ : E ⥤ D} {Δ' : D ⥤ E} (adjΔ : Δ ⊣ Δ') (ι : A ⋙ Δ ≅ B ⋙ Δ)

omit [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [F.Monoidal] [A.Monoidal]
  [B.Monoidal] in
/-- **The units of `a Δ = 1` and of `b Δ = 1` agree after `q_*`**: the comparison `θ` takes
`G (M ⟶ A' Δ' Δ A M ≅ A' Δ' Δ B M)` to `G (M ⟶ B' Δ' Δ B M)`, provided `ι : A ⋙ Δ ≅ B ⋙ Δ` is
`Δ e` on objects pulled back from `C`. -/
lemma map_unit_comp_kernelPushforwardComparison
    (hιF : ∀ X : C, ι.hom.app (F.obj X) = Δ.map (e.hom.app X)) (M : D) :
    G.map (adjA.unit.app M ≫ A'.map (adjΔ.unit.app (A.obj M) ≫ Δ'.map (ι.hom.app M))) ≫
        kernelPushforwardComparison adj adjA adjB e (Δ'.obj (Δ.obj (B.obj M))) =
      G.map (adjB.unit.app M ≫ B'.map (adjΔ.unit.app (B.obj M))) := by
  set X := adjA.unit.app M ≫ A'.map (adjΔ.unit.app (A.obj M) ≫ Δ'.map (ι.hom.app M)) with hX
  apply (adj.homEquiv _ _).symm.injective
  apply (adjB.homEquiv _ _).symm.injective
  have hn := e.inv.naturality (G.map X)
  have h₁ := adjΔ.unit.naturality (A.map (adj.counit.app M))
  have h₂ := ι.hom.naturality (adj.counit.app M)
  have h₃ := adjΔ.unit.naturality (e.hom.app (G.obj M))
  have h₄ := adjΔ.unit.naturality (B.map (adj.counit.app M))
  dsimp at hn h₁ h₂ h₃ h₄
  simp only [homEquiv_counit, Functor.map_comp, assoc, map_map_kernelPushforwardComparison_counit]
  rw [reassoc_of% hn, ← A.map_comp_assoc]
  erw [adj.counit_naturality]
  simp only [hX, A.map_comp, assoc]
  erw [adjA.counit_naturality, adjA.left_triangle_components_assoc]
  rw [← B.map_comp_assoc, ← B.map_comp_assoc, ← F.map_comp, ← G.map_comp]
  erw [adj.counit_naturality]
  simp only [B.map_comp, assoc]
  erw [adjB.counit_naturality, adjB.left_triangle_components_assoc]
  rw [reassoc_of% h₁, ← Δ'.map_comp, h₂, hιF, Δ'.map_comp, ← reassoc_of% h₃,
    Iso.inv_hom_id_app_assoc]
  exact h₄.symm

/-- **The first triangle identity from the integral along `b`.** The unit given by a kernel
satisfies the normalization at `𝟙_ D` of `CategoryTheory.Adjunction.ofTraceCounit` as soon as the
class `𝟙 ⟶ B' Δ' Δ B 𝟙 ⟶ B' (A T ⊗ B 𝟙) ≅ B' (A T)` given by the kernel has integral `1` against
the trace `t_b : B' A T ≅ F G T ⟶ F 𝟙 ≅ 𝟙` along `b` (the base change of `t` along the base
change map `F G ⟶ B' A` of `e⁻¹`). -/
lemma map_kernelAdjunctionUnit_app_comp_traceCounit (T : D)
    (κT : Δ ⋙ Δ' ⟶ tensorLeft (A.obj T)) [∀ M, IsIso (kernelComparison adj adjA e T M)]
    [∀ N, IsIso (adj.monoidalProjection T N)] (t : G.obj T ⟶ 𝟙_ C)
    [IsIso (kernelBaseChange adj adjB e.symm T)]
    (he' : ∀ X Y : C, e.inv.app (X ⊗ Y) ≫ A.map (δ F X Y) ≫ δ A (F.obj X) (F.obj Y) =
      B.map (δ F X Y) ≫ δ B (F.obj X) (F.obj Y) ≫ (e.inv.app X ⊗ₘ e.inv.app Y))
    (hιF : ∀ X : C, ι.hom.app (F.obj X) = Δ.map (e.hom.app X))
    (hint : adjB.unit.app (𝟙_ D) ≫ B'.map (adjΔ.unit.app (B.obj (𝟙_ D)) ≫
      κT.app (B.obj (𝟙_ D)) ≫ A.obj T ◁ η B ≫ (ρ_ _).hom) ≫
        kernelTraceA adj adjB e.symm T t = 𝟙 _) :
    G.map ((kernelAdjunctionUnit adj adjA e adjΔ ι T κT).app (𝟙_ D)) ≫
      (adj.traceCounit T t).app (G.obj (𝟙_ D)) = 𝟙 _ := by
  have hcore := monoidalProjectionLeft_comp_map_kernelBaseChange adj adjA adjB e he' T (𝟙_ D)
  have htr := adj.whiskerRight_leftUnitor_eq_monoidalProjectionLeft (G.obj T) t (𝟙_ D)
  have hθ := map_unit_comp_kernelPushforwardComparison adj adjA adjB e adjΔ ι hιF (𝟙_ D)
  have hθn := kernelPushforwardComparison_naturality adj adjA adjB e (κT.app (B.obj (𝟙_ D)))
  have hρ := adjB.monoidalProjection_tensorUnit (A.obj T)
  rw [← IsIso.eq_inv_comp] at hρ
  have h₂ : inv (G.map (kernelComparison adj adjA e T (𝟙_ D))) ≫
      inv (adj.monoidalProjection T (G.obj (𝟙_ D))) ≫
        adj.monoidalProjectionLeft (G.obj T) (𝟙_ D) =
      kernelPushforwardComparison adj adjA adjB e (A.obj T ⊗ B.obj (𝟙_ D)) ≫
        G.map (inv (kernelBaseChange adj adjB e.symm T ▷ 𝟙_ D ≫
          adjB.monoidalProjection (A.obj T) (𝟙_ D))) := by
    rw [IsIso.inv_comp_eq, IsIso.inv_comp_eq, ← reassoc_of% hcore, ← G.map_comp,
      IsIso.hom_inv_id, G.map_id, comp_id]
  simp only [kernelAdjunctionUnit_app, traceCounit_app, Functor.map_comp, Functor.map_inv, assoc]
  rw [htr, reassoc_of% h₂, kernelUnit, homEquiv_unit, kernelUnitTranspose,
    ← assoc (adjΔ.unit.app _), A'.map_comp, ← assoc (adjA.unit.app _), G.map_comp, assoc]
  erw [reassoc_of% hθn]
  rw [reassoc_of% hθ,
    ← G.map_comp, ← G.map_comp, ← G.map_comp, ← G.map_id]
  congr 1
  rw [IsIso.inv_comp, inv_whiskerRight, assoc, assoc, ← comp_whiskerRight_assoc,
    unitors_equal, rightUnitor_naturality, ← reassoc_of% hρ]
  simp only [kernelTraceA, Functor.map_comp, assoc] at hint ⊢
  exact hint

end Kernel

end CategoryTheory.Adjunction
