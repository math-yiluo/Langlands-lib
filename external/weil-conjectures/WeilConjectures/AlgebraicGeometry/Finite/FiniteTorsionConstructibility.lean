/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-!
# Finite-torsion constructible complexes on the pro-etale site

Source: Weil conjectures blueprint,
`literature/blueprint/master/blueprint/sec-smooth-purity/`
`sk-def-sf-operations/def-weil-finite-torsion-constructibility.md`,
node order 1454 (blueprint: definition-constructible-sheaves).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The bounded constructible finite-torsion subcategory of the derived category of
sheaves of `A_{E,n}`-modules on the small pro-etale site of `Y`.

Source: Weil conjectures blueprint, node `definition-constructible-sheaves`,
order 1454 (blueprint: definition-constructible-sheaves). The predicate is
finite support of cohomology degrees and constructibility of every cohomology sheaf;
the cited triangulated-closure theorem supplies the full triangulated structure.
-/
noncomputable def finiteTorsionConstructible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    (Y : Scheme.{u}) : ObjectProperty (proEtaleDerivedCategory Y
      (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n _hn
  fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y
        (Padic.coefficientExtensionRing l E n)
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y
            (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)

/-- The finite-torsion predicate is closed under isomorphisms.
Source: Weil blueprint, node order 1454
(blueprint: definition-constructible-sheaves). -/
noncomputable instance finiteTorsionConstructible_isClosedUnderIsomorphisms
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    (finiteTorsionConstructible D l hl E n hn Y).IsClosedUnderIsomorphisms :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  (proEtale_bounded_constructible_isTriangulated Y
    (Padic.coefficientExtensionRing l E n)).1

end AlgebraicGeometry.Scheme
