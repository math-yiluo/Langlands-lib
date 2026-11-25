/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.KInjectiveResolution
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! The finite-projective Hom-complex comparison used by the bounded RHom model.

Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-quasi-iso).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

private theorem homObjMap_zero_target
    {E M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (𝟙 E) (0 : M ⟶ N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private theorem homObjMap_zero_source
    {E F N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : E ⟶ F) (𝟙 N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver R.obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj U.unop).map (𝟙 N : N ⟶ N).val = 0
  ext W x
  change ((φ.app W).hom) (0) = 0
  exact map_zero _

end CategoryTheory
