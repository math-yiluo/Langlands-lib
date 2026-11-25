/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Composition calculation for étale section comparisons

Source: Stacks Project, Sites Tags 03CB and 03CC, and Étale Cohomology Tag 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Expanding the units and reassociating naturality equations needs extra elaboration fuel.
/-- The scheme-level composition calculation for two commuting triangles.

Source: Stacks Project, Sites Tags 03CB and 03CC (units of composite inverse images),
with fibre-product pasting as in Étale Cohomology Tag 09YQ.
(blueprint: lem-weil-pbc-sets-section-comparison-composition).

Proof: first substitute `h ≫ f` for `k`, and `g ≫ k` for `l`. Expand both section maps
as their adjunction units, the chosen inverse-image composition isomorphisms, and
restriction along the fibre-product pasting isomorphisms. Naturality of the `g`-unit
in the site object moves the restriction for `(h,f)` through that unit. Naturality
of the same unit in the sheaf morphism given by the `(f,h)` composition isomorphism
moves that isomorphism through the unit. Naturality of the `(k,g)` composition
isomorphism moves the resulting restriction to the last presheaf map. Apply the
associativity clause for the chosen composition isomorphisms in
`etaleSetInverseImageCompositionUnits`, for the three morphisms `f`, `h`, and `g`.
Now the `(h,g)` composition isomorphism follows the two successive units. Its unit
compatibility clause replaces those two units by the unit for `g ≫ h`, followed by
restriction along the inverse pasting map for `(g,h)`. The remaining restrictions
combine by the presheaf composition law. The associativity of fibre-product pasting,
`MorphismProperty.Over.pullbackComp_assoc`, identifies their composite with the
single pasting map for `(g ≫ h,f)`; equivalently, their projections to `U` and `V`
are the same, so pullback uniqueness identifies them. This is exactly the single
section comparison on the right. Restore `k` and `l` by equality elimination;
proof irrelevance identifies the equality witnesses. No sections are required to
exist, and none of these steps assumes a cover, directedness, or a limit cone. -/
theorem etaleSetSectionComparisonComposition
    {R S T V : Scheme.{u}} (h : T ⟶ S) (g : V ⟶ T) (f : S ⟶ R)
    (k : T ⟶ R) (l : V ⟶ R) (hk : h ≫ f = k) (hl : g ≫ k = l)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    etaleSetSectionComparison h f k hk G U ≫
        etaleSetSectionComparison g k l hl G U =
      etaleSetSectionComparison (g ≫ h) f l
        (by rw [Category.assoc, hk, hl]) G U := by
  subst k
  subst l
  let A := (MorphismProperty.Over.pullback @Etale ⊤ f).obj U
  let B := (MorphismProperty.Over.pullback @Etale ⊤ h).obj A
  let C := (MorphismProperty.Over.pullback @Etale ⊤ (h ≫ f)).obj U
  let p := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f).hom.app U
  have hn := ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback (h ≫ f)).obj G)).hom.naturality p.op
  have hs := NatTrans.congr_app
    (congrArg (fun e ↦ e.hom) ((Adjunction.unit
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).naturality
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) R S T f h).hom.app G)))
    (op B)
  have hc := NatTrans.congr_app
    (congrArg (fun e ↦ e.hom)
      ((Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
        R S T V f h g G)) (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj B))
  have hn' := (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) R T V (h ≫ f)
      g).hom.app G).hom.naturality ((MorphismProperty.Over.pullback @Etale ⊤ g).map p).op
  change ((Scheme.etaleSetPullback (h ≫ f)).obj G).obj.map p.op ≫
      ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback (h ≫ f)).obj G)).hom.app (op C) =
    ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback (h ≫ f)).obj G)).hom.app (op B) ≫
      ((Scheme.etaleSetPullback g).obj ((Scheme.etaleSetPullback (h ≫ f)).obj G)).obj.map
      ((MorphismProperty.Over.pullback @Etale ⊤ g).map p).op at hn
  change (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) R S T f h).hom.app
      G).hom.app (op B) ≫
      ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback (h ≫ f)).obj G)).hom.app (op B) =
    ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback h).obj ((Scheme.etaleSetPullback f).obj G))).hom.app (op B) ≫
      ((Scheme.etaleSetPullback g).map (((Classical.choose
      etaleSetInverseImageCompositionUnits.2.2) R S T f h).hom.app G)).hom.app (op
      ((MorphismProperty.Over.pullback @Etale ⊤ g).obj B)) at hs
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    eqToHom_refl, Category.comp_id] at hc
  simp only [etaleSetSectionComparison, eqToHom_refl,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hs, reassoc_of% hn', reassoc_of% hc]
  have hu : ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback f).obj G)).hom.app (op A) ≫
      ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (T.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback h).obj ((Scheme.etaleSetPullback f).obj G))).hom.app (op B) ≫
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) S T V h g).hom.app
      ((Scheme.etaleSetPullback f).obj G)).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤
      g).obj B)) =
    ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ (g ≫ h)) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback f).obj G)).hom.app (op A) ≫
      ((Scheme.etaleSetPullback (g ≫ h)).obj ((Scheme.etaleSetPullback f).obj G)).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app A).op := by
    apply ConcreteCategory.hom_ext
    intro x
    simp only [comp_apply]
    exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
        S T V h g ((Scheme.etaleSetPullback f).obj G) A x
  rw [reassoc_of% hu]
  have ht := (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) R S V f (g ≫
      h)).hom.app G).hom.naturality
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app A).op
  rw [reassoc_of% ht]
  simp only [← Functor.map_comp, ← op_comp]
  have hp := congrArg (fun e ↦ e.hom.app U)
    (MorphismProperty.Over.pullbackComp_assoc (P := @Etale) (Q := ⊤) g h f)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hp
  dsimp only [p] at ⊢
  rw [hp]
  change ((Adjunction.unit (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ (g ≫ h)) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (V.smallGrothendieckTopology @Etale))).app
      ((Scheme.etaleSetPullback f).obj G)).hom.app (op A) ≫
      (((Classical.choose etaleSetInverseImageCompositionUnits.2.2) R S V f (g ≫ h)).hom.app
      G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ (g ≫ h)).obj A)) ≫
      ((Scheme.etaleSetPullback (g ≫ h ≫ f)).obj G).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app A).op ≫
      ((Scheme.etaleSetPullback (g ≫ h ≫ f)).obj G).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
          (g ≫ h) f (g ≫ h ≫ f) (Category.assoc g h f).symm).hom.app U ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).hom.app A).op = _
  rw [← Functor.map_comp, ← op_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [A]
  erw [Category.comp_id]

end AlgebraicGeometry
