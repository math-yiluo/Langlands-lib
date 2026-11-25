/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkNaturality
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

/-! # Scalar compatibility of restriction on module stalks

Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3),
Definition 6.31.2 (4) (Tags 009Z, 00A1).
(blueprint: lem-sc-module-restriction-stalk-linear).
-/

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

/-- Restriction alone induces a natural linear stalk comparison, with its germ formula.
Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3),
Definition 6.31.2 (4) (Tags 009Z, 00A1).
(blueprint: lem-sc-module-restriction-stalk-linear).

Proof: Forget F to its abelian sheaf S. The slice-site equivalence identifies the
underlying presheaf of its restriction with S restricted to W. Use the additive
restriction-stalk isomorphism, obtained from the final functor of neighborhoods
in W to neighborhoods in X. Its germ formula is the displayed formula.
Represent a scalar and a module element by germs on neighborhoods in W.
Restrict both representatives to their intersection. The germ scalar multiplication
formula identifies their product with the germ of the sectionwise product. The
restriction-stalk comparison sends each such germ to the germ on its open image in X.
Apply the same scalar multiplication formula there. The forward ring comparison
cancels the inverse ring comparison used to transport scalars. This proves the
identity for every scalar and every module element. Thus the additive comparison
is linear after scalar transport. Naturality is checked on germs: both composites
send the germ of a section to the germ of its image under the module morphism.
These component maps therefore assemble to the required natural transformation. -/
theorem exists_moduleRestrictionStalk_morphism (X : RingedSpace.{u}) (W : Opens X)
    (x : X) (hx : x ∈ W) :
    ∃ c : SheafOfModules.overFunctor.{u} (moduleRings X) W ⋙
        (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
        RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩ ⋙
        ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom ⟶
      RingedSpace.moduleStalkFunctor X x,
      ∀ (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W)
        (hV : (⟨x, hx⟩ : W) ∈ V)
        (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))),
        (c.app F) (TopCat.Presheaf.germ (C := Ab.{u})
          (X := (X.restrict W.isOpenEmbedding).carrier)
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf
          V ⟨x, hx⟩ hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩ s := by
  classical
  obtain ⟨c, hc⟩ := exists_moduleRestrictionStalk_components X W x hx
  let S := SheafOfModules.overFunctor.{u} (moduleRings X) W ⋙
    (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
    RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩ ⋙
    ModuleCat.restrictScalars
      (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom
  let T := RingedSpace.moduleStalkFunctor X x
  let n : S ⟶ T :=
    { app := c
      naturality := by
        intro F G f
        exact moduleRestrictionStalk_components_natural X W x hx c hc f }
  exact ⟨n, hc⟩

end AlgebraicGeometry
