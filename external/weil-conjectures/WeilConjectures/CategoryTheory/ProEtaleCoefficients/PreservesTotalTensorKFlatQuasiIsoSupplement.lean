/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso

/-!
# Preservation of quasi-isomorphisms between K-flat complexes

Source: Weil conjectures blueprint, main-20261015, `chap-The-pro-etale-site`,
`sk-def-sfb-derived-categories`, definition `def-sfb-preserves-kflat-quasi-iso`
(blueprint: def-sfb-preserves-kflat-quasi-iso).

The binary total tensor is Mathlib's `HomologicalComplex.tensorObj`, with maps
`HomologicalComplex.tensorHom`. Its degree `n` is the coproduct indexed by pairs
`(p, q)` with `p + q = n`. The differential is `d_P ⊗ 1 + (-1)^p (1 ⊗ d_Q)`
on the `(p, q)` summand. Countable coproducts suffice for this construction;
no preservation of these coproducts by tensoring is assumed.

## Main definitions

* `CochainComplex.IsKFlatForTotalTensor`: preservation of quasi-isomorphisms by
  both binary total tensor functors.
* `CategoryTheory.Functor.PreservesTotalTensorKFlatQuasiIso`: termwise preservation
  of quasi-isomorphisms between two such complexes.
-/

@[expose] public section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]

end CategoryTheory.Functor
