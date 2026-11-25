/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons

set_option linter.privateModule false

/-! # Constant-coefficient normalization of the ringed tower square

The section-normalized ringed compositor agrees with the fixed constant-coefficient
compositor. This exposes the existing proved normalization helper for further proofs.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.rightDerivedFunctor constantSheaf

private theorem inverseComparison {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (c : Z ≅ W) (h : X = Z) :
    (c.symm ≪≫ eqToIso h.symm ≪≫ a).inv = (a.symm ≪≫ eqToIso h ≪≫ c).hom := by
  subst h
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Scheme
