/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-! # The ordinary-module presentation of derived internal Hom

Source: Stacks Project, Tags 0A5W and 0A5Y.
(blueprint: def-pur-derived-internal-hom).
The generic ringed-site definition remains publicly available. The ordinary module
presentation uses the existing K-injective right adjoint of the K-flat derived tensor;
it is an abbreviation for the existing closed internal-Hom bifunctor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace CategoryTheory

/-- Ordinary-module presentation of RHom, using the existing derived closed structure.
Its construction in `DerivedCategory.Monoidal.Closed` right derives the Hom functor
on the homotopy category using K-injective resolutions. Thus this is the ordinary
module specialization of the generic ringed-site notion, with its existing tensor-Hom
adjunction, rather than a second construction of derived Hom.
Source: Stacks 0A5W, 0A5Y (blueprint: def-pur-derived-internal-hom). -/
abbrev ordinaryModuleDerivedInternalHom (R : Type u) [CommRing R] :
    (DerivedCategory (ModuleCat.{u} R))ᵒᵖ × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  Functor.uncurry.obj MonoidalClosed.internalHom

end CategoryTheory
