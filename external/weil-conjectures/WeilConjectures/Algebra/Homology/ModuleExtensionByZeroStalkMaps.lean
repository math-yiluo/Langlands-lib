/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkInside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitions
public import Mathlib.Topology.Sheaves.Module

/-! # Stalks and maps for extension by zero of modules

Source: literature/stacks-project/sheaves.tex, Tag 00A7, clauses (2)--(4),
and the presheaf construction preceding it.
(blueprint: lem-sc-module-extension-by-zero-stalk-maps)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry

/-- The extension-by-zero stalk formula and the canonical maps for nested opens.
Extension by zero is the landed `SheafOfModules.extensionByZeroPresheaf ⋙ sheafification`
and its adjunction with restriction is the one of `open_restriction_adjunction_exact`
(chosen by `Classical.choice`, as in `open_extension_mayer_vietoris_shortExact`).
Inside an open, `G_x ≅ (j_{W,!} G)_x` is a natural isomorphism of `O_{X,x}`-modules
(the stalk of `G` on the open subspace, its scalars restricted along Mathlib's
`restrictStalkIso`), tied canonically by sending the germ of `s` to the germ of its
image under the adjunction unit. For restrictions of a global module, `e` is the
inverse of the counit's stalk map, so the last equation states that the transition
maps are identities under the common `F_x` identification. At the top open, the counit
identifies extension by zero with the identity; the top-open compatibility equation
expresses `iota W X` as the counit in this encoding.

Source: Stacks Project, Sheaves Tag 00A7, clauses (2)--(4), and Tag 00A5.
(blueprint: lem-sc-module-extension-by-zero-stalk-maps)

Proof: (1) Form the presheaf equal to `G` on opens contained in `W` and zero otherwise.
Its module sheafification has the adjunction universal property
(`def-weil-presheaf-modules-sheafification`), identifying it with the left adjoint
in `lem-sc-derived-open-restriction-adjunction-exact`. The underlying abelian
presheaf is extension by zero, so `lem-sc-topological-extension-by-zero-stalks`
gives zero stalks outside and the unit-induced stalk isomorphisms inside. They are
linear on germs by `def-weil-pbc-module-stalk`, and natural by naturality of the unit.
(2) Transpose the restriction of the unit on `W'` to define `iota W W'`.
The unit at the same open transposes to the identity. Restricting the transpose
identities twice and using uniqueness gives the composition law. At the top open
extension by zero is identified with the identity and the transpose is the counit.
(3) The counit's presheaf map is the identity on opens inside `W`, so its stalk
map there is the inverse of the stalk isomorphism from (1), by the adjunction-map
clause of `lem-sc-topological-extension-by-zero-stalks`. Apply stalk functoriality
(`def-weil-pbc-module-stalk`) to `iota W W'` followed by the counit on `W'`.
Both counit stalk maps are identities under these identifications; thus so is the
transition stalk map. -/
theorem module_extensionByZero_stalk_maps (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (G : SheafOfModules.{u} ((moduleRings X).over W)) (x : X),
      x ∉ W → IsZero ((RingedSpace.moduleStalkFunctor X x).obj
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj G))) ∧
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
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s)) ∧
    (∀ F : SheafOfModules.{u} (moduleRings X),
      IsIso ((Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F) ∧
      ∃ iota : (∀ (W W' : Opens X), W ≤ W' →
        ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F) ⟶
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
              ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))),
        (∀ (W W' : Opens X) (h : W ≤ W'),
          (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).homEquiv _ _
              (iota W W' h) =
            (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).inv.app F ≫
              (SheafOfModules.overMap (moduleRings X) (homOfLE h)).map
                ((Classical.choice (open_restriction_adjunction_exact X W').2.2.2.2).unit.app
                  ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F)) ≫
              (SheafOfModules.overFunctorMap (moduleRings X) (homOfLE h)).hom.app
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W' ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W').obj F))) ∧
        (∀ W : Opens X, iota W W le_rfl = 𝟙 _) ∧
        (∀ (W W' W'' : Opens X) (h : W ≤ W') (h' : W' ≤ W''),
          iota W W' h ≫ iota W' W'' h' = iota W W'' (h.trans h')) ∧
        (∀ W : Opens X,
          iota W ⊤ le_top ≫
              (Classical.choice (open_restriction_adjunction_exact X ⊤).2.2.2.2).counit.app F =
            (Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app F) ∧
        ∃ e : (∀ (W : Opens X) (x : X), x ∈ W →
            ((RingedSpace.moduleStalkFunctor X x).obj F ≅
              (RingedSpace.moduleStalkFunctor X x).obj
                ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                  PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                    ((SheafOfModules.overFunctor.{u} (moduleRings X) W).obj F)))),
          (∀ (W : Opens X) (x : X) (hx : x ∈ W),
            (e W x hx).inv =
              (RingedSpace.moduleStalkFunctor X x).map
                ((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).counit.app
                  F)) ∧
          (∀ (W W' : Opens X) (h : W ≤ W') (x : X) (hx : x ∈ W),
            (e W x hx).hom ≫ (RingedSpace.moduleStalkFunctor X x).map (iota W W' h) =
              (e W' x (h hx)).hom)) := by
  exact ⟨moduleExtensionByZero_stalk_outside X,
    ⟨moduleExtensionByZero_stalk_inside X, moduleExtensionByZero_stalk_transitions X⟩⟩

end AlgebraicGeometry
