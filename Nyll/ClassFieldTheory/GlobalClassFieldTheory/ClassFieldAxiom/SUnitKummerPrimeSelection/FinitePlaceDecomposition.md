# Decomposition groups in towers and at unramified places

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.FinitePlaceDecomposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves two facts about the decomposition groups of number field extensions at finite places, as defined by the library through a chosen place above the given one. They are independent of the S-unit Kummer construction that uses them.

## Main results

- `restrictAutomorphismScalars_mem_finitePlaceDecompositionGroup_of_relative_eq_top`: let `F ⊆ M ⊆ L` be number fields with L/F Galois and abelian and L/M Galois, let q be a finite place of M above the place p of F, and suppose the decomposition group of L/M at q is all of `Gal(L/M)`. Then every `τ ∈ Gal(L/M)`, viewed in `Gal(L/F)`, lies in the decomposition group of L/F at p.
- `finitePlaceDecompositionGroup_isCyclic_of_chosenUnramified`: for a finite Galois extension L/F of number fields and a finite place v of F that is unramified at the chosen place above it (`ChosenFinitePlaceIsUnramified`), the decomposition group at v is cyclic.

## Proof

For the first result, τ fixes the place of L above q, which lies over p; since `Gal(L/F)` is abelian, decomposition groups at all places above p coincide, so τ lies in the one at the chosen place. For the second, the decomposition group is isomorphic to the Galois group of the localized completion, and an unramified extension of nonarchimedean local fields has cyclic Galois group (imported).

## Points to watch

- The first result needs `Gal(L/F)` abelian, because the library's decomposition group refers to one chosen place above p.
- All fields must lie in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitKummerPrimeSelection/FinitePlaceDecomposition.lean`: the Lean file is the source byte for byte (SHA-256 `da06b04a4ba824305666d881371b78eb3dc96b1caaa296b5ba8993c4556f9cfa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
