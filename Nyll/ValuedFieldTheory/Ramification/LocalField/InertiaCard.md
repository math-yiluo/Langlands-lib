# Order of inertia equals the ramification index for local fields

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.InertiaCard`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field and `L/K` a finite Galois extension, with `L` carrying the complete discrete valuation chosen on it. The file has one theorem.

- `chosenLocalExtension_inertia_card_eq_ramificationIndex`: the inertia subgroup `inertiaSubgroup K` of the chosen valuation ring of `L` has cardinality equal to the ramification index of the chosen valuation on `L` over the canonical one on `K`.

The proof checks the hypotheses of a general theorem on the order of the inertia subgroup over a complete discrete valuation field. The residue field of `K` is finite, the residue extension is finite-dimensional, and so it is separable. This separability is the hypothesis the general theorem needs.

The ramification index is the library's `ramificationIndex` for its discrete valuation field structures. The theorem concerns only the valuation chosen on `L`, not a valuation given in advance on `L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/InertiaCard.lean`: the Lean file is the source byte for byte (SHA-256 `d29b7262fb16ffbb72a96d2e9d6973ed790428fb65366442e9d4c936d9d69afa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
