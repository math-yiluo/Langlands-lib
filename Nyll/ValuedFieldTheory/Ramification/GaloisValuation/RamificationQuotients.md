# Decreasing filtrations by normal subgroups and their quotients

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file introduces the abstract shape of a lower ramification filtration: a group `G` with a decreasing sequence of normal subgroups `G_0 ⊇ G_1 ⊇ G_2 ⊇ …` indexed by the natural numbers. It names the quotients that ramification theory uses and gives each of them a projection, an induction principle, a universal property and functoriality. Nothing in the file involves a field or a valuation.

## Main definitions

- `AntitoneNormalSubgroupFiltration G`: a structure with `lower : ℕ → Subgroup G`, each `lower n` normal, and `lower n ≤ lower m` for `m ≤ n`.
- `inertiaSubgroup` and `wildInertiaSubgroup`: abbreviations for `G_0` and `G_1`.
- The named quotients: `quotient n` is `G/G_n`; `subquotient m n` is `G_m` modulo `G_n ∩ G_m`; `gradedPiece n` is `G_n/G_(n+1)`; `tameQuotient` is `G_0/G_1`. Each carries a group instance and a `…ConcreteMulEquiv` (the identity) to the underlying Mathlib quotient.
- Projections `quotientMk`, `subquotientMk`, `gradedPieceMk`, `tameQuotientMk`, with `…_eq_one_iff` (the class is trivial exactly when the element lies in the subgroup divided out) and `…_eq_iff` (two classes agree when `σ / τ` lies there).
- Induction principles `quotient_inductionOn` and its analogues: every class has a representative.
- `quotientLift`, `subquotientLift`, `gradedPieceLift`, `tameQuotientLift`: a homomorphism killing the relevant subgroup descends.
- `quotientMap`, `subquotientMap`, `gradedPieceMap`, `tameQuotientMap`: a homomorphism `G → H` (or between the relevant subgroups) that sends the given level of one filtration into a given level of a second filtration on `H` induces a map of the named quotients; each comes with an `_apply_mk` lemma.
- Instances: all four quotients are finite when `G` is.

## Watch for

- The names "inertia" and "wild inertia" are only names for levels 0 and 1. The structure does not ask that `G_0` be all of `G`, that the intersection of the `G_n` be trivial, or that the filtration come from a valuation.
- The index set is `ℕ`. There is no level `−1` and there are no real indices.
- `subquotient m n` is defined for all `m, n`; it is `G_m/G_n` only when `m ≤ n`.
- The quotient types are separate named definitions, intended to be used through the API above rather than unfolded. Level-change maps, the Herbrand step and the valuation-defined filtrations are in other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/RamificationQuotients.lean`: the Lean file is the source byte for byte (SHA-256 `3be45f3ae8796d00ced79d05226501427d9cbd6136273aa5cd58ba7e28cb17d8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
