/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
/-- Construction of the canonical restriction transformation in the affine continuity argument.
Source: Stacks Project, Tag 03Q6, degree-zero continuity on affine neighbourhoods.
The transformation is obtained by composing the adjunction unit with restriction along the
pullback lift from each affine stage to the limiting object. Naturality is the functoriality
of restriction and the naturality of the adjunction unit.
(blueprint: affine-open-sections-canonical-transformation) -/
theorem affineOpenSections_exists_canonical_transformation
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))),
      (∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
        (H.obj F).obj.map (MorphismProperty.Over.homMk
          (B := p.Etale.obj (D.obj j))
          (pullback.lift (c.π.app j) (𝟙 c.pt) (by
            change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
            rw [Category.id_comp]
            exact hp j))
          (by exact pullback.lift_snd _ _ _)).op) := by
  have _ := hc
  let σ (j : J) : Scheme.Etale.mk (𝟙 c.pt) ⟶ p.Etale.obj (D.obj j) :=
    MorphismProperty.Over.homMk
      (pullback.lift (c.π.app j) (𝟙 c.pt) (by
        change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
        rw [Category.id_comp]
        exact hp j))
      (by exact pullback.lift_snd _ _ _)
  have hσ {i j : J} (f : i ⟶ j) : σ i ≫ p.Etale.map (D.map f) = σ j := by
    apply MorphismProperty.Over.Hom.ext
    change (σ i).left ≫ (p.Etale.map (D.map f)).left = (σ j).left
    apply pullback.hom_ext
    · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ =
        pullback.lift _ _ _ ≫ pullback.fst _ _
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
      exact c.w f
    · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
      change pullback.lift _ _ _ ≫ pullback.snd _ _ =
        pullback.lift _ _ _ ≫ pullback.snd _ _
      simp only [pullback.lift_snd]
  refine ⟨{
    app := fun j ↦ (hH.unit.app F).hom.app (op (D.obj j.unop)) ≫
      (H.obj F).obj.map (σ j.unop).op
    naturality := ?_ }, fun j ↦ rfl⟩
  intro i j f
  dsimp only [Functor.comp_map, Functor.op_map, Functor.const_obj_obj,
    Functor.const_obj_map]
  have hu : F.obj.map (D.map f.unop).op ≫
      (hH.unit.app F).hom.app (op (D.obj j.unop)) =
      (hH.unit.app F).hom.app (op (D.obj i.unop)) ≫
        (H.obj F).obj.map (p.Etale.map (D.map f.unop)).op :=
    (hH.unit.app F).hom.naturality _
  rw [Category.comp_id, ← Category.assoc, hu, Category.assoc, ← Functor.map_comp]
  congr 1
  exact congrArg (fun g ↦ (H.obj F).obj.map g.op) (hσ f.unop)
