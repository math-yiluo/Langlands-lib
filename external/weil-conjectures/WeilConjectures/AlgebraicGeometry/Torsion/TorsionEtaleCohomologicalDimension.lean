/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-!
# Numerical torsion étale cohomological dimension

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
def-kun-cd.md (blueprint: definition-cohomological-dimension).

The infimum of the finite bounds in `ℕ∞` is their least member when there is a bound,
and is infinity when there is none.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The torsion étale cohomological dimension of a quasi-compact quasi-separated scheme:
the least nonnegative bound for the cohomology of all torsion abelian étale sheaves,
or infinity if there is no bound. Source: blueprint definition-cohomological-dimension, scheme
clause (blueprint: definition-cohomological-dimension). Integer degrees above a nonnegative bound
are natural degrees. -/
noncomputable def Scheme.torsionEtaleCohomologicalDimension (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] : ℕ∞ :=
  sInf {d | ∃ n : ℕ, d = (n : ℕ∞) ∧ T.HasTorsionEtaleCohomologicalDimensionLE n}

/-- The torsion étale cohomological dimension of a quasi-compact quasi-separated morphism:
the least nonnegative bound for all higher direct images of torsion abelian étale sheaves,
or infinity if there is no bound. Source: blueprint definition-cohomological-dimension, morphism
clause (blueprint: definition-cohomological-dimension). Higher direct images are the cohomology
sheaves of the recorded bounded below derived direct image, applied to a sheaf in degree zero. -/
noncomputable def Scheme.Hom.torsionEtaleCohomologicalDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] : ℕ∞ :=
  sInf {d | ∃ n : ℕ, d = (n : ℕ∞) ∧
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion →
      ∀ (q : ℤ), (n : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
            ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))}

end AlgebraicGeometry
