# Orders forced by a natural-number Herbrand quotient

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Index`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Elementary arithmetic on the library's low-degree Tate groups. Let `G` be a finite group, `A` a multiplicative `G`-module and `σ : G`, with `HerbrandH0 G A` and `HerbrandHMinusOne G A σ` finite, and suppose `herbrandQuotient σ = n` for a natural number `n`.

- `herbrandH0_card_eq_mul_herbrandHMinusOne_card`: `#Ĥ⁰ = n · #Ĥ⁻¹`.
- `le_herbrandH0_card_of_herbrandQuotient_eq_nat`: `n ≤ #Ĥ⁰`.
- `lowDegree_card_eq_of_herbrandQuotient_eq_nat_of_le`: if moreover `0 < n` and `#Ĥ⁰ ≤ n`, then `#Ĥ⁰ = n` and `#Ĥ⁻¹ = 1`.
- `herbrandHMinusOne_subsingleton_of_herbrandQuotient_eq_nat_of_le`: under the same hypotheses `Ĥ⁻¹` is trivial.

The proofs clear the nonzero denominator of the quotient and use that a finite nonempty group has order at least `1`.

Watch for: the upper bound `#Ĥ⁰ ≤ n` is a hypothesis of the last two results, not proved here; no generator hypothesis on `σ` is used.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Index.lean`: the Lean file is the source byte for byte (SHA-256 `c2e27cefe51be40d4ebc5c6e224a8eb680adffa8c557734c4e07b14f1fd634af`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
