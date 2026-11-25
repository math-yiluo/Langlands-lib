# Polynomials vanishing on a finite set

Module `StacksCore.Algebra.Polynomial.Roots`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over an integral domain `R`, divisibility by products of linear factors and factorization of monic polynomials with enough roots.

- `Polynomial.prod_X_sub_C_dvd_iff`: for a finite set `s ⊆ R`, the product `∏ i ∈ s, (X - C i)` divides `f` if and only if every element of `s` is a root of `f`; `prod_X_sub_C_dvd` is the backward direction.
- `Polynomial.Monic.eq_prod_X_sub_C_of_card`: a monic `f` of degree at most `#s` vanishing on all of `s` equals `∏ i ∈ s, (X - C i)`.
- `Polynomial.Monic.eq_prod_X_sub_C_of_card'`: the indexed version, for roots `r i`, `i ∈ s`, with `r` injective on `s`.

The first result compares the multiset of roots of `f` with `s`, the zero polynomial being handled separately; the factorization follows by comparing two monic polynomials, one dividing the other, of the same degree.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/Algebra/Polynomial/Roots.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
