/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude

/-!
# Tor amplitude on the small pro-etale site

The tensor dependency is given on cochain representatives with a K-flat resolution.
Accordingly the vanishing condition is tested on all such resolutions of representatives
of the given derived object. K-flat resolutions exist and their tensors compute the same
derived tensor product, so this is independent of any representative or resolution choice.

## References

* Stacks Project, Cohomology on Sites, Definition 21.46.1, Tag 08FZ, (1)--(2)
* Stacks Project, Cohomology on Sites, Definition 21.46.1 (2), Tag 08FZ
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme


/-- Finite Tor amplitude means a single ordered integer interval works for every module
sheaf, rather than a separate bound for each test sheaf. -/
noncomputable def HasFiniteProEtaleTorAmplitude (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (K : proEtaleDerivedCategory Y A) : Prop :=
  ∃ a b : ℤ, HasProEtaleTorAmplitude Y A K a b

end AlgebraicGeometry.Scheme
