/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMorphism
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso
import Mathlib.Geometry.RingedSpace.Stalks

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- For a ringed space X, open W and x in W, there is a natural O_X,x-linear isomorphism from the
stalk at x of G on W (with scalars restricted along the inverse restriction-stalk ring
isomorphism) to the stalk of its sheafified extension by zero. It sends every germ of a section
over V in W to the germ of its image under the unit of the chosen extension/restriction
adjunction, over the image of V in X.

Proof: Construct the canonical extension/restriction adjunction by direct-sum injections on opens
contained in W and the module sheafification universal property. On neighborhoods contained in W,
which are cofinal at x, the presheaf has exactly one summand and its restrictions are those of G.
The resulting colimit comparison, followed by the sheafification stalk isomorphism, is an additive
isomorphism. Represent a scalar and a section on a common neighborhood to show linearity over
O_X,x, using the inverse restriction-stalk ring isomorphism for the source action. Naturality
follows from naturality of injections and sheafification. To use the particular chosen adjunction,
compare the canonical adjunction with it by the unique natural automorphism of their common left
adjoint compatible with units. Compose the canonical stalk comparison with the stalk of that
automorphism. It remains an isomorphism, and sends a germ to the germ of the chosen unit by the
unit comparison formula. This proves the displayed germ identity on every V. Source: Stacks
Project, Sheaves Lemma 00A7 (2)-(3), Lemma 00A5, and Lemma 007Z.
(blueprint: lem-sc-module-extension-by-zero-stalk-maps-inside) -/
theorem moduleExtensionByZero_stalk_inside (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (x : X) (hx : x ∈ W),
      ∃ e : (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
          RingedSpace.moduleStalkFunctor (X.restrict (Opens.isOpenEmbedding W)) ⟨x, hx⟩ ⋙
          ModuleCat.restrictScalars
            (X.toPresheafedSpace.restrictStalkIso (Opens.isOpenEmbedding W) ⟨x, hx⟩).inv.hom ≅
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
          RingedSpace.moduleStalkFunctor X x,
        ∀ (G : SheafOfModules.{u} ((moduleRings X).over W)) (V : Opens W)
          (hV : (⟨x, hx⟩ : W) ∈ V)
          (s : ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.obj (op V)),
          (e.hom.app G) (TopCat.Presheaf.germ (C := Ab.{u})
              (X := (X.restrict (Opens.isOpenEmbedding W)).carrier)
              ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.presheaf
              V ⟨x, hx⟩ hV s) =
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  G).val.presheaf
              ((Opens.isOpenEmbedding W).isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩
              (((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app
                G).val.app
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s))
 := by
  classical
  intro W x hx
  obtain ⟨t, ht⟩ := exists_moduleExtensionByZero_stalk_morphism X W x hx
  let adj := Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2
  let q := W.sheafOfModulesEquivOver (moduleRings X)
  let Y := X.restrict W.isOpenEmbedding
  have hi (G : SheafOfModules.{u} ((moduleRings X).over W)) : IsIso (t.app G) := by
    let F := (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj G
    let f := (SheafOfModules.toSheaf (moduleRings Y)).map (q.functor.map (adj.unit.app G))
    let S : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, F.val.presheaf⟩
    let c := S.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩
    have hc : (TopCat.Presheaf.stalkFunctor (X := Y.carrier) AddCommGrpCat.{u} ⟨x, hx⟩).map f.hom ≫
        c.hom =
        (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map
          (t.app G) := by
      apply TopCat.Presheaf.stalk_hom_ext (X := Y.carrier)
        ((q.functor.obj G).val.presheaf)
      intro V hV
      rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
      erw [S.restrictStalkIso_hom_eq_germ W.isOpenEmbedding V ⟨x, hx⟩ hV]
      ext s
      exact (ht G V hV s).symm
    have : IsIso (adj.unit.app G) := moduleExtensionByZero_unit_isIso X W G
    have : IsIso
        ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map
          (t.app G)) := by
      rw [← hc]
      infer_instance
    exact isIso_of_reflects_iso _
      (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})
  let : ∀ G, IsIso (t.app G) := hi
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact ⟨asIso t, ht⟩

end AlgebraicGeometry
