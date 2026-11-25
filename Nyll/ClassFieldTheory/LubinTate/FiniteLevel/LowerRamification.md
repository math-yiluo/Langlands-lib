# Lower ramification groups of standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K`, `π` a uniformizer, and `L_n` the standard Lubin–Tate level `n`, with its valuation chosen from the integral closure (the unique extension of the base valuation). The file defines the real-indexed lower ramification groups of `L_n/K` and shows that, at natural-number indices, membership is tested on the primitive point alone.

## Main definitions and results

- `standardLubinTateRealLowerRamificationGroup hπ n s`: the library's lower ramification group of `Gal(L_n/K)` at the real index `s`, formed with the chosen valuation.
- `mem_standardLubinTateRealLowerRamificationGroup_nat_iff_primitivePoint`: for a natural number `i`, `σ` lies in the lower group at `i` iff `v(σ(λ) − λ) ≥ i + 1`, where `λ` is the primitive point (a uniformizer of `L_n`) and `v` the normalized additive valuation.
- `standardLubinTateRealLowerRamificationGroup_eq_natCeil`: for real `s ≥ 0`, the lower group at `s` equals the one at `⌈s⌉`.

## Proof

The criterion uses that the valuation ring of `L_n` is generated over that of `F` by `λ`, so a congruence for `λ` gives the congruence for every integral element. The ceiling statement holds because the ramification ideal attached to `s` depends only on `⌈s⌉`.

## Points to watch

- The lower groups are the library's own real-indexed filtration `lowerRamificationGroup`, built from the chosen valuation; at a natural number `i` the condition is `v(σ(x) − x) ≥ i + 1` on integral `x`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LowerRamification.lean`: the Lean file is the source byte for byte (SHA-256 `16c18faee63cffc26120d99acb482f964a6b2d60da56cfaa946785d8f48905b2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
