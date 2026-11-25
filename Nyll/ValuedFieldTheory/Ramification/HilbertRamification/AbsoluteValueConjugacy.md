# Galois conjugacy of extensions of an absolute value

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AbsoluteValueConjugacy`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a Galois extension `L / K`, finite or infinite, and a nontrivial real absolute value `v` on `K`, the file proves that `Gal(L/K)` acts transitively on the absolute values of `L` that extend `v`. Archimedean and non-archimedean `v` are both covered.

## Main declarations

- `absoluteValueConjugate w σ`: the absolute value `x ↦ w(σ x)`; `absoluteValueConjugate_extends` and `absoluteValueExtensionConjugate` show that it again extends `v` when `w` does.
- `equivalent_exactExtensions_eq`: two extensions of a nontrivial `v` that are equivalent (one a positive power of the other) are equal.
- `absoluteValueConjugacy`: for `L / K` Galois and `v` nontrivial, any two extensions `w, w'` of `v` to `L` satisfy `w' = w ∘ σ` for some `σ ∈ Gal(L/K)`. `absoluteValueConjugacy_exists_conjugatingAlgEquiv` is the same at the level of absolute values, and `absoluteValueConjugacy_valuationClass` the statement for equivalence classes.

## Proofs

By results imported from other files, every extension is the pullback of one fixed absolute value on an algebraic closure of the completion of `K` along a `K`-embedding of `L`. Two such embeddings differ by an automorphism of `L`, since `L / K` is normal (Mathlib's `Normal.algHomEquivAut`).

## Watch for

Extensions here are exact: elements of `AbsoluteValueExtension v L`, which restrict to `v` itself on `K`, not just to an equivalent absolute value.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/AbsoluteValueConjugacy.lean`: the Lean file is the source byte for byte (SHA-256 `b2fb8b4d0328a9dad69eaafca1ee8a8ae6f23a2577dbe789c5afcb9ed096873a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
