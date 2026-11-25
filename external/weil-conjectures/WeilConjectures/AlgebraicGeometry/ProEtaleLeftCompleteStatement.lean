/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleProductsDerived
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLeftComplete

/-!
# Left completeness of the unbounded pro-étale derived category

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-left-completeness-and-hypercovers/
sk-prop-pe-left-complete/_section.md.

The strict tower and Roos model are supplied by `proposition-milnor-sequence`; the conclusion is
expressed by the canonical truncation cone in the derived category, whose point is the
original object and whose legs are the natural maps to `τ_{≥ -n}`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Blueprint `proposition-left-completeness`: the standard t-structure on the unbounded
pro-étale derived category is left complete. For every representing complex, the canonical
quotient-family map into the strict sequential Roos model of its truncation tower becomes
an isomorphism in the derived category.

Proof: (1) [def-pe-postnikov-comparison] supplies the canonical strict Postnikov tower,
its quotient-family/zero-coordinate comparison, and the strict Roos model. (2)
[proposition-left-completeness--1] proves that comparison is a quasi-isomorphism for every scheme,
ring sheaf, and unbounded complex. (3) [def-weil-abstract-derived-category] localizes
that quasi-isomorphism, yielding the stated derived-category isomorphism.
(blueprint: proposition-left-completeness)
-/
theorem left_complete (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (CategoryTheory.ringedSiteModules.{max u (t + 1)} R)]
    (K : CochainComplex
      (CategoryTheory.ringedSiteModules.{max u (t + 1)} R) ℤ) :
    IsIso (DerivedCategory.Q.map
      (AlgebraicGeometry.Scheme.ProEt.postnikovComparison K)) := by
  have := left_complete_quasiIso X R K
  infer_instance

end AlgebraicGeometry.Scheme.ProEt
