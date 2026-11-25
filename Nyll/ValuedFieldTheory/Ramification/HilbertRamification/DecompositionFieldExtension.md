# Uniqueness of the extension from the decomposition field

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be Galois (finite or infinite), `v` a nontrivial real absolute value on `K` and `w` an extension of `v` to `L`. The file shows that `w` is the only extension to `L` of the restriction of `w` to its decomposition field `Z_w`, for archimedean and non-archimedean places alike. The file's comment calls this clause (i) of a comparison between `Z_w` and `L`; other clauses are not here.

- `absoluteValueRestrictIntermediateField w E`: the restriction of `w` to an intermediate field `E`; it is nontrivial when `v` is.
- `absoluteValueExtensionOverRestriction`: `w` as an extension of its restriction.
- `decompositionField_unique_extension_over_decompositionField`: every extension `w'` of `w|Z_w` to `L` equals `w`.

Proof: conjugacy of extensions (`absoluteValueConjugacy`) gives `σ ∈ Gal(L/Z_w)` with `w' = w ∘ σ`; since the decomposition group is exactly the group fixing `Z_w`, `σ` stabilizes `w`.

Extensions (`AbsoluteValueExtension`) restrict to the given absolute value exactly, not up to equivalence.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/DecompositionFieldExtension.lean`: the Lean file is the source byte for byte (SHA-256 `b59c75ca28d06343460d1b4362a9503bc1b376908e3a52b58361c5674487a289`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
