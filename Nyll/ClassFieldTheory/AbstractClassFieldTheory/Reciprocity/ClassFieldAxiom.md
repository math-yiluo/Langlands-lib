# The class field axiom

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract class field theory a `ℤ`-representation `A` of `G` satisfies the class field axiom if, for every finite cyclic extension `L | K` with `K` finite over the base field, the Tate cohomology of `G(L|K)` with coefficients in `A_L` has order `[L:K]` in degree `0` and order `1` in degree `−1`. The file states this axiom for the actual fixed module `A_L`, viewed as a representation of the quotient `G_K / G_L`, and compares it with the integer Tate complex used elsewhere in the library.

## Main definitions and results

- `ClassFieldAxiomCohomologyData A K E`: for a finite cyclic subextension `E` of `K`, the integral Tate groups of `E.fixedRepresentation A` in degrees `0` and `−1` are finite, of cardinalities the degree of `E` and `1`.
- `SatisfiesClassFieldAxiom A`: this holds for every `K` finite over the base and every finite cyclic subextension `E` of `K`.
- `SatisfiesClassFieldAxiom.integralTateHZero_card`, `integralTateHMinusOne_card` and `integralTateHMinusOne_isZero`: read off the two orders and the vanishing in degree `−1`.
- For `G` in universe `0` and `A` with carrier in universe `0`: `ClassFieldAxiomCohomologyData.ofOriginal` and `iff_original`, and `SatisfiesClassFieldAxiom.iff_original`, show the axiom is equivalent to the same four conditions for the library's `tateCohomology`. The lemmas `tateHZero_card`, `tateHMinusOne_card` and `tateHMinusOne_isZero` give the conclusions in that form.

The comparisons rest on the imported results that the universe-independent integral Tate groups have the same finiteness, cardinality and vanishing as the original ones.

## Points to watch

- `SatisfiesClassFieldAxiom` is a definition of a proposition, a hypothesis for later reciprocity results; the file proves nothing about any particular `A`.
- Finiteness is stored separately before cardinalities are formed, because `Nat.card` of an infinite type is `0`.
- The general statement lets the group and the coefficient carrier live in independent universes; the comparison with `tateCohomology` is proved only in universe `0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean`: the Lean file is the source byte for byte (SHA-256 `241d7b8e232975fdc5b451949149e28994b7f62c4977131169eb5678b3a9de27`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
