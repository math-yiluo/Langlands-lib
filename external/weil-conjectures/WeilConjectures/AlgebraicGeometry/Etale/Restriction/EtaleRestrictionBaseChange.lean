/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement

/-! # Scalar restriction and the open base-change mate

Source: Stacks Project, Tags 0F7J and 0GL6.
(blueprint: lem-sf-etale-restriction-open-base-change).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

private theorem exact_unit_plus
    {R : Type (u + 1)} [CommRing R] {X Y : Scheme.{u}}
    {J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {P : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} [J.Additive] [P.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits J]
    [CategoryTheory.Limits.PreservesFiniteColimits J]
    [CategoryTheory.Limits.PreservesFiniteLimits P]
    [CategoryTheory.Limits.PreservesFiniteColimits P]
    (a : J ⊣ P)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    DerivedCategory.Plus.ι.map (a.mapDerivedCategoryPlusAdjunction.unit.app K) =
      a.mapDerivedCategoryAdjunction.unit.app K.obj := by
  rw [Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Etale
