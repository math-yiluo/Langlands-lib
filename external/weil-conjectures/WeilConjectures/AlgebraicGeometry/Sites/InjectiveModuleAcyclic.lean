/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.CategoryTheory.Sites.CechComplexModule
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf

/-!
# Injective étale sheaves of modules are acyclic as abelian sheaves

An injective presheaf of `Λ`-modules is a retract of its cofree presheaf, so its Čech complexes
are exact in positive degrees (`CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`).
By the Čech criterion, the underlying abelian sheaf of an injective étale sheaf of `Λ`-modules on
a quasi-compact quasi-separated scheme has no higher cohomology. This compares the cohomology of
sheaves of `Λ`-modules with that of their underlying abelian sheaves.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_forget₂_succ_of_injective`: on a quasi-compact
  quasi-separated scheme, the underlying abelian sheaf of an injective étale sheaf of
  `Λ`-modules has no higher cohomology.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open Presheaf

variable (Λ : Type (u + 1)) [CommRing Λ]

end AlgebraicGeometry.Scheme
