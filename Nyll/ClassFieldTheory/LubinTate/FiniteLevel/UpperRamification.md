# Herbrand functions and upper ramification groups of the standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field K with uniformizer π and the standard finite Lubin–Tate level Lₙ/K, a Galois extension carrying its chosen integral-closure valuation, the file names the ramification data of Gal(Lₙ/K) by specializing the library's constructions for an extension with a unique extended valuation.

## Main definitions

- `standardLubinTateLowerRamificationFiltration hπ n`: the lower ramification filtration, as an antitone filtration by normal subgroups.
- `standardLubinTateHerbrandFunction hπ n` and `standardLubinTateInverseHerbrandFunction hπ n`: the Herbrand function φ and its inverse ψ, as functions ℝ → ℝ.
- `standardLubinTateRealUpperRamificationGroup hπ n t`: the upper ramification group at a real number t.

## Main results

- `standardLubinTateRealUpperRamificationGroup_herbrandFunction`: the upper group at φ(s) equals the real lower ramification group at s.

## Watch for

- All objects are the library's own constructions (`...OfUniqueExtension`), not Mathlib's.
- The file only defines these objects and records one compatibility; it does not compute the upper groups of Lₙ.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/UpperRamification.lean`: the Lean file is the source byte for byte (SHA-256 `a9423a77027bcc3db3746c9304dea52d8dcc14673ba5502bc62ac0338fa3b100`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
