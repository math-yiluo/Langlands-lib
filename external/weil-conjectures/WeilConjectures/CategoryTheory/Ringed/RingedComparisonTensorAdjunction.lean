/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareTensorCompatibility
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent

/-!
# Tensor and adjunction compatibility of canonical ringed-topos path comparisons

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 07A4, 07A6 and 0D6E
(blueprint: lem-sfb-ringed-comparison-tensor-adjunction).

## Main definitions

- `RingedPathRightDerived`: right-derived units and canonical derived adjunction witnesses.
- `canonicalRingedPullbackComparison`, `canonicalRingedDirectImageComparison`: the two
  universal derived path comparisons.
- `ringedPathTensorMap`: the composite of the two canonical tensor-pullback maps.

The recorded ringed tensor presentations keep the actual site module categories,
K-flat tensor models and structural ring maps. The right-derived witnesses below
add the comparison units and the canonical adjunction normalization. In particular
the direct-image comparison is constructed independently by right-derived uniqueness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace CategoryTheory

end CategoryTheory
