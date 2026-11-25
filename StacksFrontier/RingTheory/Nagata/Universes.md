# Nagata algebras in independent universes

Module `StacksFrontier.RingTheory.Nagata.Universes`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves permanence of the Nagata condition for finite type algebras whose Lean universe can differ from that of the base.

For a commutative base ring A in universe u with `StacksIsNagataRing A`, `StacksIsNagataRing.of_finiteType` gives `StacksIsNagataRing S` for any finite type A-algebra S in universe v.

The proof presents S as a quotient of a polynomial ring in finitely many variables in A's universe, applies the same-universe theorem (item (2) of `isNagataRing_tfae`), and transports along a ring isomorphism with `MonogenicN1.isNagataRing_of_ringEquiv`.

The module docstring also announces a result for algebras essentially of finite type, which the file does not contain, and calls the theorem by a name without the `Stacks` prefix.

Stacks Project Tag 0334.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Universes.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `IsNagataRing.of_essFiniteType`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsNagataRing.of_finiteType` is `StacksIsNagataRing.of_finiteType` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
