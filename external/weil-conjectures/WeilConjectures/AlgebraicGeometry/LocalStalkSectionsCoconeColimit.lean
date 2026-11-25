/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsCanonicalColimit
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero continuity for a cofiltered system of affine open subschemes.
Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
(blueprint: new-local-stalk-sections-cocone-colimit)

Proof: Fix one stage. Its upper tail is cofinal in the cofiltered index category.
Every stage of this tail is affine and maps to the fixed affine stage by an open
immersion, hence by an affine morphism. The limit cone remains a limit on the tail.
The coordinate rings form a filtered diagram, and the spectrum of their colimit
is the scheme limit. Apply Tag 03Q6 in degree zero over the fixed affine stage,
to the restriction of F there and the identity morphism of that stage. This gives
an isomorphism from the colimit of stage sections to sections of the inverse image
on c.pt. Inverse image along an open immersion is restriction, so its stage
sections are precisely F(D_j). Identify the inverse image on the limit with H
by uniqueness of left adjoints to the given direct image. The isomorphism
intertwines adjunction units. The terminal-to-base-change map is the displayed
pullback lift, so these identifications send the continuity maps to ν. Therefore
the comparison from the colimit to the point of Cocone.mk _ ν is an isomorphism,
which proves its colimit universal property. The coefficient universe is kept
fixed throughout: the affine-site argument uses only the values of the supplied
sheaves and their given adjunction, without choosing a larger coefficient category.
Zero sheaves are included. The index is nonempty by cofilteredness; no global
quasi-separatedness assumption on X is needed, since the fixed stage is affine. -/
theorem affineOpenSections_cocone_isColimit
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
    (ν : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν : ∀ j, ν.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    Nonempty (IsColimit (Cocone.mk _ ν)) := by
  obtain ⟨ν₀, hν₀, hcol⟩ := affineOpenSections_exists_canonical_colimit
    D c p hp hc H hH F
  have h_eq : ν = ν₀ := by
    apply NatTrans.ext
    funext j
    exact (hν (unop j)).trans (hν₀ (unop j)).symm
  rw [h_eq]
  exact hcol
