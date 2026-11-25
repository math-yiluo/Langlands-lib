/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Definitions for the inverse-image tensor-hom comparison

Shared definitions for the normalized comparison of inverse image with tensor products and
internal homs.

## References

* Stacks Project, Tags 03EK, 03CY, 03D2 and 09A5
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- Extension of scalars after inverse image, for the coefficient-extension clause. -/
noncomputable abbrev inverseImageScalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)) :
    SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O')) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} (J := ProEt.topology X)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α)
    ((proEtaleModuleInverseImage g O).obj F)

/-- A pure tensor followed by module sheafification. -/
noncomputable def purTensorSection {X : AlgebraicGeometry.Scheme.{u}}
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F G : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (s : F.val.obj (op V)) (t : G.val.obj (op V)) :
    ((SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} G).obj F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.siteTensorPresheaf F.val G.val).presheaf).app (op V)
      (s ⊗ₜ[O.obj.obj (op V)] t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual module inverse-image unit on sections, using the recorded small model. -/
noncomputable def purInverseImageSection {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (O : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : Y.ProEt) (s : F.val.obj (op V)) :
    ((proEtaleModuleInverseImage g O).obj F).val.obj
      (op ((proEtaleBaseChange g).obj V)) :=
  (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit g O)).unit.app
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O)).obj F)).val.app
        (op (AsSmall.up.obj V))) s

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pure scalar-extension sections, in the recorded mixed-universe construction. -/
noncomputable def purScalarSection {X : AlgebraicGeometry.Scheme.{u}}
    (O O' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (α : O ⟶ O')
    (F : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O))
    (V : X.ProEt) (b : O'.obj.obj (op V)) (s : F.val.obj (op V)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α F).val.obj
      (op V) :=
  (CategoryTheory.toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheafOfUniverses α F).presheaf).app (op V)
      (b ⊗ₜ[O.obj.obj (op V), (α.hom.app (op V)).hom] s)

end AlgebraicGeometry.Scheme
