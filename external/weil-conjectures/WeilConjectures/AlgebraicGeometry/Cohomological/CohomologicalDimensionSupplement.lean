/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Torsion étale cohomological dimension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
def-sc-etale-torsion-cd.md (blueprint: definition-cohomological-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- For a scheme `X`, torsion étale cohomological dimension at most `c` means
that every torsion abelian sheaf on the small étale site has vanishing ordinary
derived-section cohomology in every degree greater than `c`.  The torsion
condition is the local-section condition `CategoryTheory.Sheaf.IsTorsion`.
(Source: blueprint node `definition-cohomological-dimension`; (blueprint:
definition-cohomological-dimension).) -/
def HasTorsionEtaleCohomologicalDimensionLE (X : Scheme.{u}) (c : ℕ) : Prop :=
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    F.IsTorsion →
      ∀ (q : ℕ), c < q →
        Subsingleton
          ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))

end AlgebraicGeometry.Scheme

end
