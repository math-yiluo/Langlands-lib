# Hilbert 90 and Tate cohomology of units in degree −1

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Hilbert90`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite field extension `L/K` whose automorphism group `Gal(L/K)` is cyclic, with a chosen generator, the file shows that the Tate cohomology of the units `Lˣ` in degree −1 is trivial.

- `unitsTateHminusOne_card_eq_one`: for `FiniteDimensional K L` and `g : Gal(L/K)` such that every automorphism is a power of `g`, the group `tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)` has `Nat.card` equal to 1.

The proof transports the cardinality along the cyclic comparison `unitsH1IsoTateHminusOne` between `H¹` and `Ĥ⁻¹`, and uses that `H¹` of the unit representation has exactly one element (Hilbert 90, available as a uniqueness instance).

The docstring presents this as the `i = −1` half of the local class-field-axiom theorem. No Galois or locality hypothesis is made: `Gal(L/K)` is the group of `K`-algebra automorphisms of `L`, and only cyclicity with a given generator is assumed. In Lean, `K` and `L` are taken in `Type` (universe 0).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Hilbert90.lean`: the Lean file is the source byte for byte (SHA-256 `d554b302ae3c5e1b5481edd364597cb9af5818884a1462f3c1512247c140f278`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
