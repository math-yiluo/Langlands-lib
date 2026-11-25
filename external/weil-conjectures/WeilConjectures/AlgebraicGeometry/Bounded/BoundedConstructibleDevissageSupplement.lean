/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissage

/-! # Finite truncation dévissage for constructible module objects

This is the standard t-structure induction from blueprint
`proposition-six-operations-dctf--14`, step 10. It is independent of coefficient finiteness:
only the target property is required to be triangulated.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open DerivedCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale


end AlgebraicGeometry.ProEtale
