# Proof that the dimension-at-most-one property is closed under subobjects and quotients

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.DimensionLEOneClosedUnderSubobjectsQuotients`
(module `Langlands.CategoryTheory.AbelianSubcategoryStatement`, by
Worker 633). The statement and its supporting definition
`dimensionLEOneProperty` are unchanged and imported by their Lean names.

## Theorem

Module `Langlands.CategoryTheory.DimensionLEOneClosureProof` contains

```lean
theorem Langlands.CategoryTheory.dimensionLEOneClosedUnderSubobjectsQuotients_proof
    (K : Type u) [Field K] :
    DimensionLEOneClosedUnderSubobjectsQuotients K
```

It holds for every field `K` in every universe `u`, with no characteristic
restriction. The property is the actual one on `ModuleCat.{u} K`,
`fun V => FiniteDimensional K V ∧ Module.finrank K V ≤ 1`, including the
finite-dimensionality conjunct. The theorem proves the three conjuncts of
the statement:

1. `(dimensionLEOneProperty K).ContainsZero`;
2. `(dimensionLEOneProperty K).IsClosedUnderSubobjects`: for every ambient
   monomorphism `f : X ⟶ Y` in `ModuleCat.{u} K`, the property of `Y`
   implies that of `X`;
3. `(dimensionLEOneProperty K).IsClosedUnderQuotients`: for every ambient
   epimorphism `f : X ⟶ Y`, the property of `X` implies that of `Y`.

Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Source

This is the first half of the counterexample to Renard 2026, Appendix
A.VI.1, printed page 261 / one-based PDF page 267 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). The
printed sentence claims that every full subcategory of A-mod closed under
submodules and quotients is abelian. This theorem shows that the
dimension-at-most-one subcategory meets these closure hypotheses. The
companion results `DimensionLEOneLineHasNoBinaryProduct` and
`DimensionLEOneNotAbelian` show that it is still not abelian. The
counterexample is derived content following the public note
`notes/renard/appendix-a-corrections.md`, not a claim of the book. The
statement companion `Langlands/CategoryTheory/AbelianSubcategoryStatement.md`
records the source analysis.

## Implemented proof

- **Zero.** The witness is `ModuleCat.of K PUnit`. It is a zero object by
  `ModuleCat.isZero_of_subsingleton`. It is finite-dimensional by instance
  search, and its finrank is `0` by `Module.finrank_zero_of_subsingleton`,
  hence at most `1`.
- **Subobjects.** Let `f : X ⟶ Y` be a monomorphism with `Y` in the property.
  `ModuleCat.mono_iff_injective` makes the underlying linear map `f.hom`
  injective. `FiniteDimensional.of_injective` then makes `X`
  finite-dimensional. `LinearMap.finrank_le_finrank_of_injective` gives
  `finrank K X ≤ finrank K Y ≤ 1`.
- **Quotients.** Let `f : X ⟶ Y` be an epimorphism with `X` in the property.
  `ModuleCat.epi_iff_surjective` makes `f.hom` surjective.
  `FiniteDimensional.of_surjective` then makes `Y` finite-dimensional.
  `LinearMap.finrank_le_finrank_of_surjective` gives
  `finrank K Y ≤ finrank K X ≤ 1`.

The closure parts quantify over every ambient monomorphism and epimorphism
exactly as the Mathlib classes do. They are not restricted to chosen
submodules or quotient constructions. All results used are from Mathlib
(commit `5ed2965256430c3649e86755f9576b54eca72435`). No Library result other
than the statement is used.

## Scope

This file proves only the closure statement. It works in unital
`ModuleCat.{u} K`, with module carriers in the field's universe. A formal
embedding into the book's possibly nonunital module category is a separate
adapter obligation. The file imports only the statement module and adds no
other file.
