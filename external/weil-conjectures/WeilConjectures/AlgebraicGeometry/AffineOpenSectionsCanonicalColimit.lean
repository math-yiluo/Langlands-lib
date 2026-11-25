/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsCanonicalTransformation
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsCanonicalColimitCore

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- The geometric continuity core: a canonical restriction cocone is colimiting.
Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
(blueprint: new-local-stalk-sections-canonical-colimit)

The proof is the affine-site continuity argument over a cofiltered limit of affine
open subschemes.  It identifies the filtered colimit of sections with sections on
the limit, then transports the result across the supplied adjunction.  This
intermediate statement isolates the geometric part; the parent theorem only
identifies a supplied cocone with this canonical one.
-/
theorem affineOpenSections_exists_canonical_colimit
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
          (by exact pullback.lift_snd _ _ _)).op) ∧
        Nonempty (IsColimit (Cocone.mk _ ν₀)) := by
  obtain ⟨ν₀, hν₀⟩ := affineOpenSections_exists_canonical_transformation
    D c p hp hc H hH F
  exact ⟨ν₀, hν₀, affineOpenSections_canonical_colimit_core
    D c p hp hc H hH F ν₀ hν₀⟩
