/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! Scalar restriction and the ordinary ringed inverse-image square.

## References

* Stacks Project, Tags 03D7, 03D8 and 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients exchangeModuleComposition

section
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW SW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aW : RW ⟶ SW) (aZ : RZ ⟶ SZ)
    (ckR : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (chR : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (ckS : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj SV ≅ SW)
    (chS : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj SW ≅ SZ)
    (hk : ckR.hom ≫ aW = (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map aV ≫ ckS.hom)
    (hh : chR.hom ≫ aZ = (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map aW ≫ chS.hom)

end

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

set_option linter.defProp false in
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
