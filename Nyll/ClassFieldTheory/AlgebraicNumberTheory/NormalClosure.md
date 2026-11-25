# The normal closure of an extension of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For an extension `L/K` of number fields, this file fixes the Galois closure used in the library's global theory: the normal closure of `L` over `K` formed inside Mathlib's algebraic closure of `K`, together with a chosen copy of `L` in it.

## Main definitions and results

- `finiteNormalClosure K L`: Mathlib's `IntermediateField.normalClosure K L (AlgebraicClosure K)`, the compositum of the images of all `K`-embeddings of `L` into the algebraic closure. Instances make it a number field and a Galois extension of `K`.
- `finiteNormalClosureEmbedding K L`: a `K`-embedding of `L` into this closure, obtained from an embedding into the algebraic closure supplied by `IsAlgClosed.lift`. `finiteNormalClosureOriginalField` is its image, and `finiteNormalClosureOriginalFieldEquiv` the isomorphism of `L` onto it.
- `finiteNormalClosureOriginalField_normalClosure_eq_top`: the copy of `L` generates the closure under its `K`-conjugates, so the closure is the normal closure of that copy.
- `normalClosure_eq_top_of_source_algEquiv`: a general lemma, for arbitrary field extensions: if `L ≃ₐ[K] E` and the normal closure of `L` in `M` is all of `M`, the same holds for `E`.
- `finrank_le_finiteNormalClosure`: `[L : K] ≤ [finiteNormalClosure K L : K]`.
- `algEquivBaseOfFinrankEqOne`: an extension of degree one is isomorphic to `K` as a `K`-algebra.

## Proof

The Galois instance is obtained by turning the chosen embedding into an `L`-algebra structure on the algebraic closure, locally, and using Mathlib's results on normal closures. The generation statement combines Mathlib's characterization of `IsNormalClosure` with the transfer lemma above.

## Points to watch

- The closure itself does not depend on any choice, but the embedding of `L` into it, and therefore the distinguished copy of `L`, is fixed by `IsAlgClosed.lift`, a choice. The closure is a `K`-algebra; it is not given a global `L`-algebra structure here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NormalClosure.lean`: the Lean file is the source byte for byte (SHA-256 `3bb6f827dd0017c3ac514f1b6c2af7952ac767c6097ee2449f328dd6e867515f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
