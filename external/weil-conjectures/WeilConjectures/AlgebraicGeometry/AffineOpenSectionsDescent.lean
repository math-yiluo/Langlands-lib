/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenEtaleMapFactorization
import WeilConjectures.AlgebraicGeometry.AffineOpenInverseImageUnitRepresentatives

/-! # Every section of the inverse image on the affine limit descends to an affine stage. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Every section of the inverse image on the affine limit descends to an affine stage.
Source: Stacks Project, Tag 03Q6, degree zero of lemma-colimit, proof steps (1)--(3);
Sites, Tag 0A35, lemma-pullback-to-limit; Etale Cohomology, Tag 0EYL.
Proof: Obtain a unit representative of t on an arbitrary étale X-object U, with
ψ from the terminal object to its pullback. This is the inverse-image section step,
separated as affineOpenSections_inverse_image_unit_representatives. The first projection
of ψ defines q from the limit to U, over X. Since U is étale, it is locally of finite
presentation. Mathlib's affine-limit morphism factorization theorem gives a stage j
and g : D(j) to U over X whose composite with the cone projection is q.
Let γ be this étale-site morphism and let σ be the canonical terminal-to-pullback map
of D(j). The pullback universal property proves σ followed by p^*γ equals ψ: the
first projection is the factorization equation, and the second is the equation over
the limit. Choose s = F(γ)(b). Naturality of the adjunction unit, the supplied formula
hν₀, and functoriality identify ν₀(s) with the representative equation for t.
The geometric factorization includes empty limits and singleton diagrams; the remaining
section lemma records the corresponding sheaf edge cases. No target signature changes.
(blueprint: affine-open-sections-descent) -/
theorem affineOpenSections_descent
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
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν₀ : ∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    ∀ t : (H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))),
      ∃ (j : J) (s : F.obj.obj (op (D.obj j))), ν₀.app (op j) s = t := by
  let T := Scheme.Etale.mk (𝟙 c.pt)
  let σ (j : J) : T ⟶ p.Etale.obj (D.obj j) :=
    MorphismProperty.Over.homMk
      (pullback.lift (c.π.app j) (𝟙 c.pt) (by
        change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
        simpa only [Category.id_comp] using hp j))
      (by exact pullback.lift_snd _ _ _)
  intro t
  obtain ⟨U, ψ, b, hb⟩ := affineOpenSections_inverse_image_unit_representatives
    D c p hp hc H hH F t
  obtain ⟨j, g, hg, hgj⟩ := affineOpenSections_etale_map_factorization D c p hp hc
    U (ψ.left ≫ pullback.fst _ _) (by
      have hw : ψ.left ≫ pullback.snd U.hom p = 𝟙 c.pt :=
        MorphismProperty.Over.w ψ
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun k ↦ ψ.left ≫ k) (pullback.condition (f := U.hom) (g := p))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k ↦ k ≫ p) hw).trans (Category.id_comp p)))))
  let γ : D.obj j ⟶ U := MorphismProperty.Over.homMk g hg
  have hσ : σ j ≫ p.Etale.map γ = ψ := by
    apply MorphismProperty.Over.Hom.ext
    change (σ j).left ≫ (p.Etale.map γ).left = ψ.left
    apply pullback.hom_ext
    · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst]
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ g = _
      rw [pullback.lift_fst_assoc]
      exact hgj
    · rw [Category.assoc, Scheme.Hom.etale_map_left_comp_snd]
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd]
      exact (MorphismProperty.Over.w ψ).symm
  refine ⟨j, F.obj.map γ.op b, ?_⟩
  rw [hν₀ j]
  change (H.obj F).obj.map (σ j).op
    ((hH.unit.app F).hom.app (op (D.obj j)) (F.obj.map γ.op b)) = t
  have hu := (hH.unit.app F).hom.naturality_apply γ.op b
  change (hH.unit.app F).hom.app (op (D.obj j)) (F.obj.map γ.op b) =
    (H.obj F).obj.map (p.Etale.map γ).op
      ((hH.unit.app F).hom.app (op U) b) at hu
  erw [hu]
  erw [← Functor.map_comp_apply]
  have heq : (p.Etale.map γ).op ≫ (σ j).op = ψ.op := by
    rw [← op_comp, hσ]
  rw [heq]
  exact hb
