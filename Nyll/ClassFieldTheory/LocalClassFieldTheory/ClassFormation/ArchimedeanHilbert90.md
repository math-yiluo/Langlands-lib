# Hilbert 90 for local blocks at every place

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanHilbert90`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite cyclic Galois extension with generator `σ`, `vK` a nontrivial absolute value on `K` (archimedean or not), and `w` an extension of `vK` to `L`. The decomposition group `D` of `w` acts on the units of the local extension `L_w` of the completion `K_vK`, realised by the library's `LocalizedCompletion vK w`. This file shows that the Herbrand group `H⁻¹(D, L_wˣ)` is trivial. This is the degree `−1` half of the local class-formation axiom; it rests only on Hilbert 90, not on local reciprocity, and so holds at infinite places too.

## Main results

Both statements assume `σ` generates `Gal(L/K)` (`hgen`), and use the cyclic generator of `D` derived from `σ` (`subgroupGeneratorOfGenerator`).

- `localHerbrandHMinusOne_subsingleton`: `HerbrandHMinusOne D (LocalizedCompletion vK w)ˣ` is a subsingleton.
- `localHerbrandHMinusOne_card_eq_one_of_absoluteValue`: it has exactly one element.

## Proofs

The library's equivalence `localHerbrandHMinusOneEquivUnitsTateHminusOne` identifies this group with the Tate cohomology group in degree `−1` of the Galois group of `L_w/K_vK` acting on `L_wˣ`; that group is zero by the library's cyclic Hilbert 90 (`hilbert90_unitsTateHminusOne_isZero`).

## Remarks

- `K` and `L` live in `Type` (universe 0).
- The structures needed on the completions (algebra structures, finiteness, Galois property, the action of `D` on local units) are bound with `let` inside the statements.
- `HerbrandHMinusOne` is the library's own Herbrand group for a cyclic group with a chosen generator.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ArchimedeanHilbert90.lean`: the Lean file is the source byte for byte (SHA-256 `bacfda9f4dc69d31e0f2cf6f1833a5c40b5cabef9a3e005fb9734d1ca3b36245`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
