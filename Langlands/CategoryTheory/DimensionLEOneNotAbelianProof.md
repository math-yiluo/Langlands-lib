# Proof that the dimension-at-most-one subcategory is not abelian

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.DimensionLEOneNotAbelian`
(module `Langlands.CategoryTheory.AbelianSubcategoryStatement`, by
Worker 633). The statement and its supporting definitions are unchanged and
imported by their Lean names.

## Theorem

Module `Langlands.CategoryTheory.DimensionLEOneNotAbelianProof` contains

```lean
theorem Langlands.CategoryTheory.dimensionLEOneNotAbelian_proof
    (K : Type u) [Field K] :
    DimensionLEOneNotAbelian K
```

It holds for every field `K` in every universe `u`, with no characteristic
restriction. It proves `¬ Nonempty (Abelian (DimensionLEOneModuleCat K))`.
So no abelian structure exists on the full subcategory of
`ModuleCat.{u} K` cut out by
`FiniteDimensional K V ∧ Module.finrank K V ≤ 1`, with Mathlib's induced
category structure. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Source

This completes the counterexample to the sentence of Renard 2026, Appendix
A.VI.1, printed page 261 / one-based PDF page 267 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). That
sentence claims that every full subcategory of A-mod closed under submodules
and quotients is abelian. The published statement
`DimensionLEOneClosedUnderSubobjectsQuotients` gives the closure
hypotheses for this subcategory, and this theorem shows that it is not
abelian. The counterexample is derived content following the public note
`notes/renard/appendix-a-corrections.md`, not a claim of the book. The
statement companion `Langlands/CategoryTheory/AbelianSubcategoryStatement.md`
records the source analysis.

## Implemented proof

Assume an abelian structure `hab : Abelian (DimensionLEOneModuleCat K)`. It
becomes a local instance. Mathlib's `Abelian` class contains
`HasFiniteProducts`, so instance search gives
`HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)`. The
category structure is the fixed induced one, so this is the product notion
of the no-product statement. The published theorem
`Langlands.CategoryTheory.dimensionLEOneLineHasNoBinaryProduct_proof` from
module `Langlands.CategoryTheory.DimensionLEOneNoProductProof` refutes it.

## Scope

This file proves only the no-abelian-structure statement. It imports
`Langlands.CategoryTheory.DimensionLEOneNoProductProof` (which imports the
statement module) and adds no other file. It works in unital
`ModuleCat.{u} K`. A formal embedding into the book's possibly nonunital
module category is a separate adapter obligation.
