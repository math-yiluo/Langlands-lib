# Henselian pairs and finite algebras: Jacobson radical and adic completeness

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file collects consequences of Henselian pairs and adic completeness for finite modules and finite algebras: Nakayama-type statements on the Jacobson radical, transport of adic separatedness and precompleteness along linear equivalences, completeness of finite modules over a noetherian complete ring, and two facts on Henselian discretely valued fields.

## Main results

- `ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite`: if `I` lies in the Jacobson radical of `R` and `S` is a module-finite `R`-algebra, then `I S` lies in the Jacobson radical of `S`. `ideal_map_le_jacobson_bot_of_henselianRing_of_moduleFinite` is the case where `R` is Henselian along `I`; companion lemmas place `I • M` in the module Jacobson radical.
- `isHausdorff_map_algebraMap_of_henselianRing_of_moduleFinite`: for `R` Henselian along `I` and `S` module-finite and noetherian, `S` is `I S`-adically separated.
- `isHausdorff_of_linearEquiv`, `isPrecomplete_of_linearEquiv` and their `iff` forms: `I`-adic separatedness and precompleteness are invariant under linear equivalence.
- `isAdicComplete_of_moduleFinite`: a finite module over a noetherian `I`-adically complete ring is `I`-adically complete, in any universe (`isAdicComplete_of_moduleFinite_sameUniverse` is the case where ring and module share a universe).
- `henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete`: a module-finite algebra `S` over a noetherian `I`-adically complete `R` is Henselian along `I S`.
- `HenselianDVF.isHausdorff_maximalIdeal`: the valuation ring of a Henselian DVF is separated for its maximal ideal; hence `isAdicComplete_maximalIdeal_of_isPrecomplete`: precompleteness gives adic completeness.

## Proofs

The Jacobson statement passes to `S/Q` for a maximal `Q` and applies Nakayama to the finite `R`-module `S/Q`. Completeness of finite modules uses Mathlib's isomorphism between the adic completion of a finite module over a noetherian ring and its tensor product with the completion of the ring; the general-universe case goes through `Shrink`. Henselianity then follows from completeness by Mathlib's instance for adically complete rings.

## Caveats

Separatedness of the Henselian DVF is derived from the Jacobson condition and noetherianity, not from completeness; precompleteness is still a hypothesis for the completeness statement.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean`: the Lean file is the source byte for byte (SHA-256 `b34e3be99f59318b7ddff2fddbaab79407f83695a22b0e31fb2f7ee5ede1972d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
