/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsComparisonMap
import WeilConjectures.AlgebraicGeometry.LocalStalkSectionsAffineVanishing

/-! # Descent of equality for local-scheme sections

Source: Stacks Project, Tag 03Q6, degree zero of Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- Descent of equality for local-scheme sections.
Source: Stacks Project, Tag 03Q6, degree zero and proof steps (1)-(3).
(blueprint: new-local-stalk-sections-descent-equality)

Proof: Restrict the given sections to a common affine neighbourhood A of x.
Principal opens of A containing x are cofinal among neighbourhoods, and their
coordinate rings have colimit O_X,x. Apply degree-zero continuity in Tag 03Q6 to
the identity morphism of A, which is quasi-compact and quasi-separated. Equality
after inverse image to Spec(O_X,x) descends to equality on a principal neighbourhood
of x. Its inclusions into U and V give f and g in the opposite neighbourhood
category and the required equality of restrictions. The maps used in continuity
are the pullback maps given by the inverse-image unit and the local-scheme maps
to each open. For the displayed H, use uniqueness of left adjoints to direct image:
the natural isomorphism with standard inverse image intertwines the units. Hence
it identifies those maps with the legs of LocalStalkSections.cocone, proving the
assertion for the supplied adjunction. No henselian assumption is used. If either
representative is zero the same argument applies; empty X has no x. -/
theorem localStalkSections_descent_equality
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U V : (OpenNhds x)ᵒᵖ)
    (s : (LocalStalkSections.neighbourhoodDiagram i x F).obj U)
    (t : (LocalStalkSections.neighbourhoodDiagram i x F).obj V)
    (h : (LocalStalkSections.cocone i hi x H hH F).ι.app U s =
      (LocalStalkSections.cocone i hi x H hH F).ι.app V t) :
    ∃ (W : (OpenNhds x)ᵒᵖ) (f : U ⟶ W) (g : V ⟶ W),
      (LocalStalkSections.neighbourhoodDiagram i x F).map f s =
        (LocalStalkSections.neighbourhoodDiagram i x F).map g t := by
  obtain ⟨A, hA, hxA, hAU⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := U.unop.1 ⊓ V.unop.1) ⟨U.unop.2, V.unop.2⟩
  let A' : (OpenNhds x)ᵒᵖ := op ⟨A, hxA⟩
  let f : U ⟶ A' := (homOfLE (show A'.unop ≤ U.unop from
    fun y hy ↦ (hAU hy).1)).op
  let g : V ⟶ A' := (homOfLE (show A'.unop ≤ V.unop from
    fun y hy ↦ (hAU hy).2)).op
  let D := LocalStalkSections.neighbourhoodDiagram i x F
  let c := LocalStalkSections.cocone i hi x H hH F
  have hf : c.ι.app A' (D.map f s) = c.ι.app U s :=
    ConcreteCategory.congr_hom (c.w f) s
  have hg : c.ι.app A' (D.map g t) = c.ι.app V t :=
    ConcreteCategory.congr_hom (c.w g) t
  have hz : c.ι.app A' (D.map f s - D.map g t) = 0 := by
    rw [map_sub, hf, hg, h, sub_self]
  obtain ⟨W, k, hk⟩ := localStalkSections_affine_vanishing
    i hi x H hH F A' hA (D.map f s - D.map g t) hz
  refine ⟨W, f ≫ k, g ≫ k, ?_⟩
  have he : D.map k (D.map f s) = D.map k (D.map g t) := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hk)
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using he
