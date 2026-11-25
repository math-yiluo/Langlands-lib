# Ramification filtrations do not depend on the chosen valuation

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The lower and upper ramification groups of a finite extension of discretely valued fields depend only on the valuation ring of the top field. The file proves this, then applies it to the finite Galois levels `E` of the algebraic closure of a complete discretely valued field `K`: the filtrations built from the valuation chosen on `E` in the companion file agree with those built from any other complete discrete valuation on `E` extending that of `K`.

## Main results

General form, for discretely valued fields `K`, `L` and two target structures `target`, `target'` on `L` that extend the base valuation uniquely and have the same valuation ring:

- `lowerRamificationGroup_eq_of_valuationSubring_eq`: the real lower ramification groups `G_s` coincide for every real `s`.
- `lowerRamificationFiltration_eq_of_valuationSubring_eq`: the integral lower filtrations coincide.
- `herbrandFunction_eq_of_valuationSubring_eq`, `inverseHerbrandFunction_eq_of_valuationSubring_eq` (`L/K` finite): the Herbrand function and its inverse coincide.
- `upperRamificationGroup_eq_of_valuationSubring_eq` (`L/K` finite): the upper groups coincide.

At a finite Galois level `E`, for any `target : CompleteDVF E` extending the base valuation:

- `chosenIntegralClosureTarget_valuation_isEquiv` and `chosenIntegralClosureTarget_valuationSubring_eq`: the chosen valuation is equivalent to that of `target`, with the same valuation ring.
- `hasUniqueValuationExtension_of_finiteGaloisLevel` and its DVF form: `target` also extends the base valuation uniquely.
- `chosenLowerRamificationGroup_eq`, `chosenLowerRamificationFiltration_eq`, `chosenHerbrandFunction_eq`, `chosenInverseHerbrandFunction_eq`, `chosenUpperRamificationGroup_eq`: the chosen lower groups, lower filtration, Herbrand functions and upper groups equal those formed from `target`.

## Proofs

Equal valuation rings give a ring isomorphism between them that preserves the maximal ideal, its powers (the ideals defining the real lower groups) and the action of `Gal(L/K)`, so membership in `G_s` is the same. The Herbrand functions are built from the lower filtration and therefore agree; the upper groups are lower groups at the inverse Herbrand function. At a finite Galois level the two valuations are equivalent by uniqueness of the extension, hence have the same ring.

## Points to watch

The general statements take unique extension of the valuation for both targets as explicit hypotheses (`huniq`, `huniq'`); only at finite Galois levels is uniqueness derived, from the chosen target.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteGaloisLevelIndependence.lean`: the Lean file is the source byte for byte (SHA-256 `0675543228b71012b40c2a754a00c9cb0be9aa2b2db0aa284a599a9710d74c1d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
