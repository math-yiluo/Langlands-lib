/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMaps

/-! # Restriction of extension by zero on an open

Source: Stacks Project, Tag 00A7 (4).
(blueprint: lem-pc-open-extension-restriction-iso).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Restricting extension by zero to the original open gives the identity functor.
Source: Stacks Project, Tag 00A7 (4), and Modules on Sites, Tag 03DI.
(blueprint: lem-pc-open-extension-restriction-iso).

Proof: Choose the extension-by-zero/restriction adjunction from
`open_restriction_adjunction_exact`. Transfer its unit to module sheaves on U through
`sheafOfModulesEquivOver`, and forget to abelian sheaves. At each point of U, the
interior stalk comparison in `module_extensionByZero_stalk_maps` is an isomorphism.
Its germ formula identifies it with the stalk map of the unit followed by the
canonical restriction-stalk isomorphism: apply stalk hom extensionality, rewrite the
restriction-stalk germ formula, and use the given unit germ formula. Hence the stalk
map of the unit is an isomorphism. Mathlib's stalk criterion makes the underlying
abelian sheaf map an isomorphism. The module forgetful functor and the equivalence
reflect isomorphisms, so each unit component is an isomorphism. Its inverse is the
claimed natural isomorphism. The empty open has no stalks to check, and the total
open uses exactly the same argument. -/
theorem nonempty_openExtensionRestrictionIso (X : RingedSpace.{u}) (U : Opens X) :
    Nonempty
      ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
        SheafOfModules.overFunctor.{u} (moduleRings X) U ≅
          𝟭 (SheafOfModules.{u} ((moduleRings X).over U))) := by
  classical
  let adj := Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2
  let q := U.sheafOfModulesEquivOver (moduleRings X)
  let Y := X.restrict (Opens.isOpenEmbedding U)
  have hu (G : SheafOfModules.{u} ((moduleRings X).over U)) : IsIso (adj.unit.app G) := by
    let F := (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
      PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj G
    let f := (SheafOfModules.toSheaf (moduleRings Y)).map (q.functor.map (adj.unit.app G))
    have hs (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := by
      obtain ⟨e, he⟩ := (module_extensionByZero_stalk_maps X).2.1 U x.val x.property
      let S : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, F.val.presheaf⟩
      let c := S.restrictStalkIso U.isOpenEmbedding x
      have hc : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom ≫ c.hom =
          (forget₂ (ModuleCat.{u} (X.presheaf.stalk x.val)) AddCommGrpCat.{u}).map
            (e.hom.app G) := by
        apply TopCat.Presheaf.stalk_hom_ext (X := Y.carrier)
          ((q.functor.obj G).val.presheaf)
        intro V hx
        rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
        erw [S.restrictStalkIso_hom_eq_germ U.isOpenEmbedding V x hx]
        ext s
        exact (he G V hx s).symm
      have hcomp : IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom ≫ c.hom) := by
        rw [hc]
        infer_instance
      exact IsIso.of_isIso_comp_right _ c.hom
    let : ∀ x : U, IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) := hs
    have : IsIso f := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f
    have : IsIso (q.functor.map (adj.unit.app G)) :=
      isIso_of_reflects_iso _ (SheafOfModules.toSheaf (moduleRings Y))
    exact isIso_of_reflects_iso _ q.functor
  let : ∀ G, IsIso (adj.unit.app G) := hu
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app adj.unit
  exact ⟨(asIso adj.unit).symm⟩

end AlgebraicGeometry
