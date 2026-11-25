/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Étale sheaves form Grothendieck abelian categories

Let `X` be a scheme. The categories of abelian sheaves and of sheaves of `Λ`-modules on the
small étale site of `X`, with values in the universe `u + 1` one above that of `X`, are
Grothendieck abelian; in particular they have enough injectives. These are the cases used in
étale cohomology of the general instance
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology`.

## References

- Stacks Project, Lemma 18.15.1 / Tag 03DA, Theorem 19.12.6 / Tag 079H
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Abelian sheaves on the small étale site form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_sheaf_smallEtaleTopology_addCommGrpCat :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Sheaves of `Λ`-modules on the small étale site form a Grothendieck abelian category. -/
@[stacks 03DA]
theorem isGrothendieckAbelian_sheaf_smallEtaleTopology_moduleCat (Λ : Type (u + 1)) [Ring Λ] :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  inferInstance

/-- Sheaves of `Λ`-modules on the small étale site have enough injectives, since they form a
Grothendieck abelian category. The case `Λ = ℤ` gives abelian sheaves. -/
@[stacks 079H]
theorem enoughInjectives_sheaf_smallEtaleTopology_moduleCat (Λ : Type (u + 1)) [Ring Λ] :
    EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- Abelian sheaves on the small étale site have enough injectives. -/
theorem enoughInjectives_sheaf_smallEtaleTopology_addCommGrpCat :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

end AlgebraicGeometry.Scheme
