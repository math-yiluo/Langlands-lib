# Image and kernel of the Artin map at a finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field, L/K a finite abelian extension, and v a finite place of K. The library's Artin homomorphism at v, `chosenFinitePlaceArtinMonoidHom v : K_vˣ → Gal(L/K)`, is built from a chosen place above v. This file computes its image and kernel.

## Main results

- `chosenFinitePlaceArtinMonoidHom_range`: the image is `finitePlaceDecompositionGroup v`, the decomposition group of the chosen place above v.
- `chosenFinitePlaceArtinMonoidHom_ker`: the kernel is `chosenFinitePlaceLocalNormSubgroup v`, the local norm group of the chosen completion L_w/K_v, carried into K_vˣ by the identification of the two completions of K at v.

## Proof

Both follow from the factorization of the map as the local Artin map of L_w/K_v followed by the isomorphism of Gal(L_w/K_v) with the decomposition group. Local reciprocity supplies surjectivity of the local Artin map (`Universe.abelianLocalArtinMonoidHom_surjective`) and its kernel, the local norm group (`Universe.abelianLocalArtinMonoidHom_ker`).

## Points to watch

- Both statements are about the chosen place above v, and the decomposition group and norm group are the chosen ones.
- These are the library's local Artin maps and norm groups, resting on its local class field theory.
- `NumberField L` is not assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Core.lean`: the Lean file is the source byte for byte (SHA-256 `2e275aa18e07d0917631bf1408ccbf91ec1621fccf06206250695ba448c03c38`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
