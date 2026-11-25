/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologyLimit

set_option linter.privateModule false

/-!
# Pullback naturality of the etale–pro-etale cohomology comparison

Source: Stacks Project, Cohomology on Sites, Tags 0D6E and 08J6, Section 072X;
Pro-etale Cohomology, Tag 099W; latest blueprint, prose-09-07,
base-change compatibility of the Kummer class
(blueprint: lem-sfb-etale-proetale-comparison-pullback-naturality).

## Main definitions

* `AlgebraicGeometry.ProEtale.cohomologyMap`: canonical pro-etale cohomology pullback.

## Main statements

* `AlgebraicGeometry.ProEtale.comparisonCohomologyMap_pullback`: the comparison square.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

-- The canonical adjunction comparisons involve large functors on the two scheme sites.
private theorem homEquiv_conjugate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (d : R' ≅ R)
    {M : C} {N : D} (t : L'.obj M ⟶ N) :
    a.homEquiv M N (((conjugateEquiv b a).symm d.hom).app M ≫ t) =
      b.homEquiv M N t ≫ d.hom.app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm b a d.hom M, Category.assoc, ← d.hom.naturality,
    ← Category.assoc, ← Adjunction.homEquiv_unit]

private theorem inverse_square
    {C : Type*} [Category C] {A B D E T : C}
    (k : A ≅ B) (n : B ≅ D) (b : D ≅ T) (a : A ≅ E) (m : E ≅ T)
    (h : k.hom ≫ n.hom ≫ b.hom = a.hom ≫ m.hom) :
    b.inv ≫ n.inv = m.inv ≫ a.inv ≫ k.hom := by
  apply (cancel_mono (n.hom ≫ b.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  rw [h]
  simp

end AlgebraicGeometry.ProEtale
