/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of data living on quasi-compact opens of a stage

Let `{Fⱼ}` be a cofiltered system of quasi-compact quasi-separated schemes with affine transition
maps and limit cone `c`, and let `V` be a quasi-compact open of a stage `F_λ`. We show that

- an inclusion of opens of `V` (the first one quasi-compact) which holds after pulling back to
  the limit holds at some later stage (`AlgebraicGeometry.exists_forall_resLE_preimage_le`);
- two morphisms out of `V` to a scheme locally of finite type over a base which agree in the
  limit agree at some later stage (`AlgebraicGeometry.exists_forall_resLE_comp_eq`);
- a morphism out of the preimage of `V` in the limit to a scheme locally of finite presentation
  over a base descends to the preimage of `V` at some later stage
  (`AlgebraicGeometry.exists_resLE_comp_eq_of_locallyOfFinitePresentation`).

Stages past `λ` are objects `k : Over λ`, and "for every later stage" is expressed by quantifying
over all `k'` with a morphism `k' ⟶ k` in `Over λ`. These are the variants of the eventual
equality and descent statements for limits of schemes used for the overlaps of a relative gluing
datum.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

lemma Scheme.Hom.resLE_eq_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.resLE U V e = f'.resLE U V e' := by
  subst h
  rfl

lemma Scheme.Opens.mem_ι_image_iff_exists {X : Scheme.{u}} (V : X.Opens) (A : V.toScheme.Opens)
    (x : X) : x ∈ V.ι ''ᵁ A ↔ ∃ h : x ∈ V, (⟨x, h⟩ : V) ∈ A := by
  rw [← SetLike.mem_coe, Scheme.Hom.coe_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨_, hx, rfl⟩

/-- An inclusion of preimages of opens of `V` under a restriction of `f` is an inclusion of
preimages under `f` of their images in `Y`. -/
lemma Scheme.Hom.resLE_preimage_le_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (A₁ A₂ : V.toScheme.Opens) :
    f.resLE V (f ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₁ ≤ f.resLE V (f ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₂ ↔
      f ⁻¹ᵁ (V.ι ''ᵁ A₁) ≤ f ⁻¹ᵁ (V.ι ''ᵁ A₂) := by
  constructor
  · intro H x hx
    obtain ⟨h, hA⟩ := (V.mem_ι_image_iff_exists A₁ _).mp hx
    have hxV : x ∈ f ⁻¹ᵁ V := h
    have key : f.resLE V (f ⁻¹ᵁ V) le_rfl ⟨x, hxV⟩ = ⟨f x, h⟩ :=
      Subtype.ext (f.coe_resLE_apply le_rfl _)
    have h₁ : (⟨x, hxV⟩ : (f ⁻¹ᵁ V : X.Opens)) ∈ f.resLE V (f ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₁ := by
      rw [Scheme.Hom.mem_preimage, key]
      exact hA
    have h₂ := H h₁
    rw [Scheme.Hom.mem_preimage, key] at h₂
    exact (V.mem_ι_image_iff_exists A₂ _).mpr ⟨h, h₂⟩
  · intro H x hx
    rw [Scheme.Hom.mem_preimage] at hx ⊢
    have e : f.resLE V (f ⁻¹ᵁ V) le_rfl x = ⟨f x.1, x.2⟩ :=
      Subtype.ext (f.coe_resLE_apply le_rfl _)
    rw [e] at hx ⊢
    obtain ⟨_, h⟩ := (V.mem_ι_image_iff_exists A₂ _).mp
      (H ((V.mem_ι_image_iff_exists A₁ _).mpr ⟨x.2, hx⟩))
    exact h

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ Scheme.{u}} {c : Cone F}
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (F.map f)]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (F.map f)] in
/-- Restricting along the composite of two transition maps. -/
lemma resLE_map_comp {l : I} (V : (F.obj l).Opens) {k j : I} (f : j ⟶ l) (g : k ⟶ j) :
    (F.map (g ≫ f)).resLE V (F.map (g ≫ f) ⁻¹ᵁ V) le_rfl =
      (F.map g).resLE (F.map f ⁻¹ᵁ V) (F.map (g ≫ f) ⁻¹ᵁ V)
        (by rw [Functor.map_comp, Scheme.Hom.comp_preimage]) ≫
        (F.map f).resLE V (F.map f ⁻¹ᵁ V) le_rfl := by
  rw [Scheme.Hom.resLE_comp_resLE]
  exact Scheme.Hom.resLE_eq_of_eq (F.map_comp g f) _ _ _ _

include hc in
/-- An inclusion of opens of a quasi-compact open `V ⊆ F_λ` which holds in the limit holds past
some stage. -/
theorem exists_forall_resLE_preimage_le {l : I} (V : (F.obj l).Opens)
    (A₁ A₂ : V.toScheme.Opens) (hA₁ : IsCompact (A₁ : Set V.toScheme))
    (H : (c.π.app l).resLE V (c.π.app l ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₁ ≤
      (c.π.app l).resLE V (c.π.app l ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₂) :
    ∃ k₀ : Over l, ∀ (k : Over l) (_ : k ⟶ k₀),
      (F.map k.hom).resLE V (F.map k.hom ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₁ ≤
        (F.map k.hom).resLE V (F.map k.hom ⁻¹ᵁ V) le_rfl ⁻¹ᵁ A₂ := by
  rw [Scheme.Hom.resLE_preimage_le_iff] at H
  have hc₁ : IsCompact ((V.ι ''ᵁ A₁ : (F.obj l).Opens) : Set (F.obj l)) := by
    rw [Scheme.Hom.coe_image]
    exact hA₁.image V.ι.continuous
  obtain ⟨j, f, hf⟩ := exists_map_preimage_le_map_preimage F c hc hc₁ H
  refine ⟨Over.mk f, fun k g ↦ ?_⟩
  rw [Scheme.Hom.resLE_preimage_le_iff, ← Over.w g, Functor.map_comp, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ hf

include hc in
/-- An inclusion of preimages of opens of a stage, the first one quasi-compact, which holds in
the limit holds past some stage. -/
theorem exists_forall_map_preimage_le {l : I} {U V : (F.obj l).Opens}
    (hU : IsCompact (U : Set (F.obj l))) (H : c.π.app l ⁻¹ᵁ U ≤ c.π.app l ⁻¹ᵁ V) :
    ∃ k₀ : Over l, ∀ (k : Over l) (_ : k ⟶ k₀), F.map k.hom ⁻¹ᵁ U ≤ F.map k.hom ⁻¹ᵁ V := by
  obtain ⟨j, f, hf⟩ := exists_map_preimage_le_map_preimage F c hc hU H
  refine ⟨Over.mk f, fun k g ↦ ?_⟩
  rw [← Over.w g, Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ hf

variable [∀ i, QuasiSeparatedSpace (F.obj i)]

omit [IsCofiltered I] [∀ i, QuasiSeparatedSpace (F.obj i)] in
lemma compactSpace_opensDiagram_obj {l : I} {V : (F.obj l).Opens}
    (hV : IsCompact (V : Set (F.obj l))) (k : Over l) :
    CompactSpace ((opensDiagram F l V).obj k) :=
  isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := F.map k.hom) _ V.2 hV)

instance quasiSeparatedSpace_opensDiagram_obj {l : I} (V : (F.obj l).Opens) (k : Over l) :
    QuasiSeparatedSpace ((opensDiagram F l V).obj k) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (F.map k.hom ⁻¹ᵁ V).2).mp
    (.of_quasiSeparatedSpace _)

variable {S : Scheme.{u}} (t : F ⟶ (Functor.const I).obj S)

/-- The structure morphism of the system of preimages of `V` to the base `S`. -/
@[simps] noncomputable def opensDiagramStructure (l : I) (V : (F.obj l).Opens) :
    opensDiagram F l V ⟶ (Functor.const (Over l)).obj S where
  app k := (F.map k.hom ⁻¹ᵁ V).ι ≫ t.app k.left
  naturality k k' g := by
    simp only [opensDiagram_map, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [Scheme.Hom.resLE_comp_ι_assoc, t.naturality]
    simp

omit [∀ i, QuasiSeparatedSpace (F.obj i)] in
include hc in
/-- Two morphisms out of a quasi-compact open `V ⊆ F_λ` over `S` to a scheme locally of finite
type over `S` which agree in the limit agree past some stage. -/
theorem exists_forall_resLE_comp_eq {l : I} {V : (F.obj l).Opens}
    (hV : IsCompact (V : Set (F.obj l))) {Z : Scheme.{u}} (q : Z ⟶ S) [LocallyOfFiniteType q]
    (a₁ a₂ : V.toScheme ⟶ Z) (ha₁ : a₁ ≫ q = V.ι ≫ t.app l) (ha₂ : a₂ ≫ q = V.ι ≫ t.app l)
    (H : (c.π.app l).resLE V (c.π.app l ⁻¹ᵁ V) le_rfl ≫ a₁ =
      (c.π.app l).resLE V (c.π.app l ⁻¹ᵁ V) le_rfl ≫ a₂) :
    ∃ k₀ : Over l, ∀ (k : Over l) (_ : k ⟶ k₀),
      (F.map k.hom).resLE V (F.map k.hom ⁻¹ᵁ V) le_rfl ≫ a₁ =
        (F.map k.hom).resLE V (F.map k.hom ⁻¹ᵁ V) le_rfl ≫ a₂ := by
  have := compactSpace_opensDiagram_obj hV
  let r := (F.map (Over.mk (𝟙 l)).hom).resLE V (F.map (Over.mk (𝟙 l)).hom ⁻¹ᵁ V) le_rfl
  have hr (k : Over l) (g : k ⟶ Over.mk (𝟙 l)) :
      (opensDiagram F l V).map g ≫ r = (F.map k.hom).resLE V (F.map k.hom ⁻¹ᵁ V) le_rfl := by
    simp only [opensDiagram_map, r, Scheme.Hom.resLE_comp_resLE]
    exact Scheme.Hom.resLE_eq_of_eq (by rw [← F.map_comp, Over.w g]) _ _ _ _
  have hπ : (opensCone F c l V).π.app (Over.mk (𝟙 l)) ≫ r =
      (c.π.app l).resLE V (c.π.app l ⁻¹ᵁ V) le_rfl := by
    simp only [opensCone_π_app, r, Scheme.Hom.resLE_comp_resLE]
    exact Scheme.Hom.resLE_eq_of_eq (c.w _) _ _ _ _
  obtain ⟨k, g, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (opensDiagram F l V) (opensDiagramStructure t l V) q (opensCone F c l V)
    (isLimitOpensCone F c hc l V) (i := Over.mk (𝟙 l)) (r ≫ a₁) (r ≫ a₂)
    (by simp [r, ha₁]) (by simp [r, ha₂])
    (by rw [reassoc_of% hπ, reassoc_of% hπ, H])
  refine ⟨k, fun k' g' ↦ ?_⟩
  have e := congrArg ((opensDiagram F l V).map g' ≫ ·) hk
  simp only [← Category.assoc, ← Functor.map_comp, hr k' (g' ≫ g)] at e
  exact e

include hc in
/-- A morphism over `S` out of the preimage in the limit of a quasi-compact open `V ⊆ F_λ` to a
scheme locally of finite presentation over `S` descends to the preimage of `V` at some later
stage. -/
theorem exists_resLE_comp_eq_of_locallyOfFinitePresentation {l : I} {V : (F.obj l).Opens}
    (hV : IsCompact (V : Set (F.obj l))) {Z : Scheme.{u}} (q : Z ⟶ S)
    [LocallyOfFinitePresentation q] (φ : (c.π.app l ⁻¹ᵁ V).toScheme ⟶ Z)
    (hφ : φ ≫ q = (c.π.app l ⁻¹ᵁ V).ι ≫ c.π.app l ≫ t.app l) :
    ∃ (k : Over l) (ψ : (F.map k.hom ⁻¹ᵁ V).toScheme ⟶ Z),
      ψ ≫ q = (F.map k.hom ⁻¹ᵁ V).ι ≫ t.app k.left ∧
        (c.π.app k.left).resLE (F.map k.hom ⁻¹ᵁ V) (c.π.app l ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, c.w]) ≫ ψ = φ := by
  have := compactSpace_opensDiagram_obj hV
  obtain ⟨k, ψ, h₁, h₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (opensDiagram F l V) (opensDiagramStructure t l V) q (opensCone F c l V)
    (isLimitOpensCone F c hc l V) φ (by
      ext k
      simp only [NatTrans.comp_app, opensCone_π_app, opensDiagramStructure_app,
        Functor.const_obj_obj, Functor.const_map_app, Scheme.Hom.resLE_comp_ι_assoc, hφ]
      have e : t.app k.left = F.map k.hom ≫ t.app l := by simp
      rw [e, ← Category.assoc (c.π.app k.left), c.w])
  exact ⟨k, ψ, h₂, h₁⟩

end AlgebraicGeometry
