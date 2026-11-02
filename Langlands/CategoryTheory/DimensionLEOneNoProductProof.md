# Proof that the line has no binary product in the dimension-at-most-one subcategory

Author: Worker 894. This file proves the published statement
`Langlands.CategoryTheory.DimensionLEOneLineHasNoBinaryProduct`
(module `Langlands.CategoryTheory.AbelianSubcategoryStatement`, by
Worker 633). The statement and its supporting definitions
`dimensionLEOneProperty`, `DimensionLEOneModuleCat` and `dimensionLEOneLine`
are unchanged and imported by their Lean names.

## Declarations

Module `Langlands.CategoryTheory.DimensionLEOneNoProductProof` contains, in
namespace `Langlands.CategoryTheory`:

- `dimensionLEOneLineEndo K a : dimensionLEOneLine K ⟶ dimensionLEOneLine K`,
  a supporting definition. It is the endomorphism of the actual line `K`
  given by the linear map `LinearMap.toSpanSingleton K K a`, `x ↦ x • a`,
  packaged with `ObjectProperty.homMk`. It sends `1` to `a`.
- `dimensionLEOneLineEndo_apply_one`: `(dimensionLEOneLineEndo K a).hom.hom 1 = a`.
- `dimensionLEOneLine_prod_surjective`: if
  `HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)` holds, the
  linear map `x ↦ (p x, q x)` from the chosen product object to `K × K` is
  surjective. Here `p` and `q` are the underlying linear maps of `prod.fst`
  and `prod.snd`. This is `LinearMap.prod` of the two maps.
- The target theorem

  ```lean
  theorem Langlands.CategoryTheory.dimensionLEOneLineHasNoBinaryProduct_proof
      (K : Type u) [Field K] :
      DimensionLEOneLineHasNoBinaryProduct K
  ```

The theorem holds for every field `K` in every universe `u`, with no
characteristic restriction. It proves
`¬ HasBinaryProduct (dimensionLEOneLine K) (dimensionLEOneLine K)` in the
full subcategory `DimensionLEOneModuleCat K`. Since `HasBinaryProduct`
only asserts that some limit cone exists, this rules out every internal
product object with every pair of projections. Its axioms are `propext`,
`Classical.choice` and `Quot.sound`.

## Source

This is part of the counterexample to Renard 2026, Appendix A.VI.1, printed
page 261 / one-based PDF page 267 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`). There,
axiom AB1 requires finite products in an abelian category. The counterexample
is derived content following the public note
`notes/renard/appendix-a-corrections.md`, not a claim of the book. The
statement companion `Langlands/CategoryTheory/AbelianSubcategoryStatement.md`
records the source analysis.

## Implemented proof

Assume `HasBinaryProduct L L` for the actual line `L = dimensionLEOneLine K`,
and let `V = L ⨯ L` be the chosen product object in the full subcategory.
Write `p, q : V.obj → K` for the linear maps underlying `prod.fst` and
`prod.snd`.

1. **Surjectivity onto `K × K`.** Take `(a, b) : K × K`. The universal
   property inside the full subcategory, applied to the two endomorphisms
   `dimensionLEOneLineEndo K a` and `dimensionLEOneLineEndo K b`, gives
   `prod.lift _ _ : L ⟶ V`. Let `m` be the image of `1` under its underlying
   linear map. Evaluate `prod.lift_fst` and `prod.lift_snd` at `1` and use
   `dimensionLEOneLineEndo_apply_one`. This gives `p m = a` and `q m = b`,
   so `(p, q)` sends `m` to `(a, b)`.
2. **Dimension count.** The property of `V` gives that `V.obj` is
   finite-dimensional with `finrank K V.obj ≤ 1`.
   `LinearMap.finrank_le_finrank_of_surjective` applied to step 1 gives
   `finrank K (K × K) ≤ finrank K V.obj`. By `Module.finrank_prod` and
   `Module.finrank_self`, the left side is `2`, which contradicts `≤ 1`
   (`omega`).

The argument uses only the universal property inside the full subcategory.
It does not reduce to the ambient fact that `K × K` has dimension two. All
results used are from Mathlib (commit
`5ed2965256430c3649e86755f9576b54eca72435`). No Library result other than the
statement is used.

## Scope

This file proves only the no-product statement. The closure statement and
the no-abelian-structure statement have their own proofs. The category is
unital `ModuleCat.{u} K` with module carriers in the field's universe; a
formal embedding into the book's possibly nonunital module category is a
separate adapter obligation. The file imports only the statement module and
adds no other file.
