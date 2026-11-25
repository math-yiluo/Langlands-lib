# Unramifiedness of the two-step small Hilbert class field tower

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerUnramified`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, let `H₁ = smallHilbertClassField K` be its small Hilbert class field (norm subgroup with quotient the ideal class group) and `H₂` the second stage selected in the rational absolute class formation. This file shows that `H₂/H₁` is everywhere unramified and that the maximal abelian subextension of `H₂/K` is exactly `H₁`.

## Main results

- `smallHilbertTowerTopField K`: the fixed field `H₂`, with instances making it a number field, finite over `H₁` and over `ℚ`, and abelian Galois over `H₁` (`smallHilbertTowerTopIsAbelianGalois`). The algebra, scalar action and module structures over `H₁` are fixed by named reducible definitions installed as local instances.
- `smallHilbertTowerSecondStage_ideleClassNorm_range`: the idele-class norm range from `H₂` to `H₁` equals `smallHilbertClassFieldNormSubgroup` of `H₁`.
- `smallHilbertTowerSecondStage_isEverywhereUnramified`: `H₂/H₁` satisfies `IsEverywhereUnramified`, unramified at finite and infinite places.
- `smallHilbertTower_maximalAbelianSubextension_eq_firstStage`: the maximal abelian subextension of the Galois realization `smallHilbertTowerGaloisRealization K` equals `smallHilbertClassFieldSubextension K`.

## Proofs

Unramifiedness follows from the norm-range equality by `isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup`. For the last result, `H₁/K` and `H₂/H₁` are both everywhere unramified, so `H₂/K` is by transitivity; then `maximalAbelianSubextension_le_smallHilbertClassField_of_everywhereUnramified` gives one inclusion and `smallHilbertTowerBase_le_maximalAbelianSubextension` the other.

## Caveats

- `H₂` is the class field selected by choice in the realization file; only its norm subgroup is specified.
- "Small Hilbert class field" and `IsEverywhereUnramified` are the library's notions; the tower lives inside `SeparableClosure ℚ`, with `K` realized through the library's chosen base subgroup.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertTowerUnramified.lean`: the Lean file is the source byte for byte (SHA-256 `1b07c488f1a2e16d8b2194093adc14ec474469d9e021c685f907b34213c7d793`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
