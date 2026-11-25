# Induced filtrations on the Galois groups of a fixed field

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.FixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L / K` and a subgroup `H` of `Gal(L/K)`, the file moves a filtration `(G_n)` of `Gal(L/K)` by normal subgroups to the Galois groups of `L / L^H` and, when `H` is normal, of `L^H / K`, through Mathlib's isomorphisms `H ≃ Gal(L/L^H)` and `Gal(L/K)/H ≃ Gal(L^H/K)`.

## Main declarations

- `fixedFieldSubextensionFiltration F H`: the filtration `G_n ∩ H` on `Gal(L/L^H)`. Its `_lower` formula and its two Herbrand lemmas omit the hypothesis `IsGalois K L`.
- `fixedFieldQuotientImageFiltration F H`: the image filtration on `Gal(L^H/K)`.
- `card_fixedFieldSubextension_mul_card_fixedFieldQuotientImage`: the orders of the two groups at level `n` multiply to `|G_n|`.
- Four lemmas say that the Herbrand functions `φ` and `ψ` of these filtrations equal those of the abstract subgroup and quotient-image filtrations.

## Watch for

As in the abstract file, the filtration on `Gal(L^H/K)` is only the image of the given one. Nothing here says it is the lower ramification filtration of `L^H / K`, and no valuation enters.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/FixedField.lean`: the Lean file is the source byte for byte (SHA-256 `395a49099379afe6087b76145c99c4f7c4e1ae5d40f568240a41204bd3e1ea16`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
