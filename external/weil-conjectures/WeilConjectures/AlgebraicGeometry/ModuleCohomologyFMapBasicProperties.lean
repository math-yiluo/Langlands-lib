/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.BasicPropertiesLinearity
import WeilConjectures.AlgebraicGeometry.BasicPropertiesDegreeZero
import WeilConjectures.AlgebraicGeometry.BasicPropertiesIdentity
import WeilConjectures.AlgebraicGeometry.BasicPropertiesRestriction

/-! # Basic properties of maps on module cohomology

Source: Stacks Project, Cohomology of Sheaves, Section 01F7, Tags 01F8--01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-properties).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Linearity, degree zero, identity, and restriction properties of the map induced by an
`h`-map.  The degree-zero clause is expressed using the canonical derived-functor
identifications with global sections.
Source: Stacks Project, Cohomology of Sheaves, Section 01F7;
(blueprint: lem-weil-pbc-module-cohomology-fmap-basic-properties).

Proof plan (all parts are left as the stage-3 proof): choose injective resolutions and
use the derived-functor comparison isomorphisms. The global-sections complexes are
modules over global sections, and the comparison maps are linear, proving (1).
Left exactness identifies degree-zero cohomology with global sections; the defining
augmentation square proves (2). For (3), lift the morphism across the injective
resolution and use uniqueness up to homotopy, then apply the derived-functor
map-via-lift lemma. For (4), compare the restriction and pullback units using the
open-immersion restriction isomorphism, lift between the two injective resolutions,
and use the K-injective comparison and homotopy lemmas; cancellation of the
quasi-isomorphism gives the displayed equality. The setup uses
`lem-weil-pbc-scheme-modules-enough-injectives`,
`lem-weil-pbc-derived-functor-map-via-lift`,
`lem-weil-pbc-lift-along-injective-quasi-iso`,
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`,
`lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`, and
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`.
-/
theorem moduleCohomologyFMap_basic_properties {X Y : Scheme.{u}} (h : X ⟶ Y)
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    (φ : G ⟶ (pushforward h).obj F) (p : ℕ) :
    (∃ L : (Y.toRingedSpace.moduleCohomology p).obj G ⟶
          (ModuleCat.restrictScalars h.appTop.hom).obj
            ((X.toRingedSpace.moduleCohomology p).obj F),
      (forget₂ _ AddCommGrpCat).map L = moduleCohomologyFMap h φ p) ∧
    (∃ eG : (Y.toRingedSpace.moduleCohomology 0).obj G ≅
          (RingedSpace.globalSectionsFunctor Y.toRingedSpace).obj G,
      ∃ eF : (X.toRingedSpace.moduleCohomology 0).obj F ≅
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F,
        (forget₂ _ AddCommGrpCat).map eG.hom ≫
            (forget₂ _ AddCommGrpCat).map
              ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) =
          moduleCohomologyFMap h φ 0 ≫
            (forget₂ _ AddCommGrpCat).map eF.hom) ∧
    (∀ (Z : Scheme.{u}) (GZ FZ : SheafOfModules.{u} Z.ringCatSheaf)
      (ψ : GZ ⟶ FZ),
      moduleCohomologyFMap (𝟙 Z) ψ p =
        (forget₂ _ AddCommGrpCat).map
          ((Z.toRingedSpace.moduleCohomology p).map ψ)) ∧
    (∀ (U : Y.Opens),
      ∃ κ : (restrictFunctor U.ι).obj G ≅ (tensorPullback U.ι).obj G,
        moduleCohomologyFMap U.ι ((restrictAdjunction U.ι).unit.app G) p ≫
            (forget₂ _ AddCommGrpCat).map
              (((U : Scheme).toRingedSpace.moduleCohomology p).map κ.hom) =
          moduleCohomologyFMap U.ι
            ((Classical.choose (exists_tensorPullbackAdjunction U.ι)).unit.app G) p)
 := by
  refine ⟨moduleCohomologyFMap_basic_linearity h φ p, ?_, ?_, ?_⟩
  · exact moduleCohomologyFMap_basic_degree_zero h φ
  · intro Z GZ FZ ψ
    exact moduleCohomologyFMap_basic_identity GZ FZ ψ p
  · exact moduleCohomologyFMap_basic_restriction G p

end AlgebraicGeometry.Scheme.Modules
