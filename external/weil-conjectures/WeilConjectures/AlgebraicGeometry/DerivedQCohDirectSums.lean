/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux


/-! # Direct sums in the quasi-coherent derived category

Source: literature/stacks-project/derived-categories-of-schemes.tex,
  Lemma perfect-lemma-quasi-coherence-direct-sums
(blueprint: lem-pc-derived-qcoh-direct-sums).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For every scheme `X`, the derived category of `𝒪_X`-modules whose cohomology
sheaves are quasi-coherent has all set-indexed direct sums.
Source: literature/stacks-project/derived-categories-of-schemes.tex,
  Lemma perfect-lemma-quasi-coherence-direct-sums
(blueprint: lem-pc-derived-qcoh-direct-sums). The proof proceeds as follows. First,
by `lem-pc-derived-ambient-direct-sums`, the ambient derived category has
set-indexed coproducts represented by termwise sums, with cohomology the direct
sum of the cohomologies in each degree. Second, for a family of quasi-coherent
cohomology sheaves, express its direct sum as the filtered colimit of its finite
partial sums; `lem-weil-pbc-quasi-coherent-module-direct-sum` handles finite sums,
including the zero sum, and
`lem-weil-pbc-quasi-coherent-module-colimit-affine-sections` handles the filtered
colimit. Thus every cohomology sheaf of the ambient coproduct is quasi-coherent.
Finally, the ambient coproduct universal-property bijection restricts to the full
subcategory `schemeDerivedQCohCategory`, proving the asserted coproducts there,
including empty and singleton families. -/
theorem derivedQCohDirectSums (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    HasCoproducts.{u} (schemeDerivedQCohCategory X) := by
  let : HasCoproducts.{u} (schemeDerivedCategory X) :=
    derivedAmbientHasCoproducts X
  let (I : Type u) :
      (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  intro I
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I) (schemeDerivedQCohProperty X)

end AlgebraicGeometry
