# Adic completions along an isomorphism of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A ℚ-algebra isomorphism e : K ≃ M of number fields carries finite places to finite places, and the library already has continuous ring maps between the corresponding adic completions in both directions. This file shows those maps are mutually inverse and bundles them into one ring isomorphism, meant for transporting local Hilbert pairings.

- `finitePlaceAdicCompletionCongrEquiv e W`: for a finite place W of M, a ring isomorphism from the adic completion of K at the place corresponding to W (via `(finitePlaceCongr e).symm`) to the adic completion of M at W.

The proof makes K and M algebras over each other through e and e⁻¹, takes the two maps `finitePlaceAdicCompletionMap`, and checks both composites are the identity with the composition lemma `finitePlaceAdicCompletionMap_comp` and the identity case `finitePlaceAdicCompletionMap_self_apply`.

The bundled object is a ring isomorphism (`≃+*`); continuity and compatibility with e are not recorded in it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/FinitePlaceAdicCompletionCongrEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `3ebad48103f0d5873142279e58ced5451115c80e7731b12b2aae269776bc236e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
