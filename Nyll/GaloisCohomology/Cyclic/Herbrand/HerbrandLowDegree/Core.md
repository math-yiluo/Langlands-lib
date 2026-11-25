# The Herbrand quotient

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G`, a multiplicative `G`-module `A` and an element `σ : G`, the file defines the Herbrand quotient and proves its two basic properties.

- `herbrandQuotient σ : ℚ` is `#HerbrandH0 G A / #HerbrandHMinusOne G A σ`, defined under instances saying both groups are finite (`herbrandQuotient_eq_card_ratio` unfolds it).
- `herbrandQuotient_eq_one_of_card_eq`: equal orders give quotient `1`.
- `herbrandQuotient_finite_module_eq_one`: if `A` is finite and `σ` generates `G`, the quotient is `1`.
- `herbrandQuotient_exact_multiplicative`: for a short exact sequence `1 → A → B → C → 1` of equivariant homomorphisms (`i` injective, `j` surjective, `ker j = im i`), with `σ` generating `G` and all six groups finite, `h(B) = h(A) · h(C)`.

The last two follow, by clearing denominators, from the equality of orders for finite modules and from the six-term cardinality identity of the imported files.

Watch for: finiteness of each group is a hypothesis, except for finite `A`, where imported instances supply it; `HerbrandHMinusOne`, hence the quotient, depends on `σ`; in the exact-sequence theorem `A`, `B`, `C` share one universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean`: the Lean file is the source byte for byte (SHA-256 `d9715c3f71378584c29897b8840112dfc60cb4db24ab3f3ff8efe6d4cb55fa66`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
