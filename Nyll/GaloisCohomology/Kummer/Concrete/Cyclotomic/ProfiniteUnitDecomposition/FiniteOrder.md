# Units of ℤ̂ with vanishing free coordinate at p

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteOrder`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

- `zHatUnit_padicCoordinate_isOfFinOrder_of_freeCoordinate_eq_zero`: let `u ∈ ℤ̂ˣ` and `p` a prime. If the `p`-adic component of the free (`ℤ̂`) coordinate of `u` in `zHatUnitsDecomposition` is `0`, then the `p`-adic unit component of `u` (its image in `ℤ_pˣ`) has finite order.

By the companion lemma `zHatUnitsDecomposition_freeCoordinate`, the hypothesis says that the free part of that `p`-adic unit in the local decomposition `ℤ_pˣ ≃ (finite factor) × ℤ_p` is trivial; the unit is then the image of an element of the finite factor, so it has finite order.

The hypothesis concerns a single prime `p`; nothing is said about the other components.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/ProfiniteUnitDecomposition/FiniteOrder.lean`: the Lean file is the source byte for byte (SHA-256 `aebc358b805fb452638e3cedbe9c81c56dd1dfef5631392b88e001dc55523935`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
