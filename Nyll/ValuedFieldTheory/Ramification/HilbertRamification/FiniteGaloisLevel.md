# Chosen ramification filtrations at finite Galois levels

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` carry a complete discrete valuation (`base : CompleteDVF K`) and let `E` be a finite Galois subextension of the algebraic closure of `K`. An existence theorem for the integral closure of the valuation ring of `K` provides a complete discrete valuation on `E` extending that of `K`. This file fixes one such structure by choice and uses it to define the lower and upper ramification filtrations of `Gal(E/K)` without asking the caller for a valuation on `E`.

## Main definitions and results

- `chosenIntegralClosureData_exists`: there is a `CompleteDVF` structure on `E` whose valuation extends the base valuation, whose valuation ring is the integral closure of that of `K`, and which satisfies `[E : K] = e·f`.
- `chosenIntegralClosureTarget base E`: one such structure, chosen with `Classical.choose`. Companion facts: `instChosenIntegralClosureTargetHasExtension` (it extends the base valuation), `chosenIntegralClosureTarget_isIntegralClosure`, `chosenIntegralClosureTarget_isDefectless`.
- `chosenIntegralClosureTarget_hasUniqueValuationExtension` and `chosenIntegralClosureTarget_hasUniqueDVFValuationExtension`: the extension of the valuation to `E` is unique, in the complete-DVF and in the DVF formulation, from `hasUniqueValuationExtension_of_finite_separable`.
- `chosenLowerRamificationFiltration base E`: the lower ramification filtration of `Gal(E/K)` built from this unique extension, as an antitone filtration by normal subgroups.
- `chosenUpperRamificationFiltration base E`, `chosenUpperRamificationGroup base E t`: the upper ramification group for real `t`, built with the inverse Herbrand function.
- `chosenLowerRamificationGroup_normal`, `chosenUpperRamificationGroup_normal`: the groups are normal; `chosenLowerRamificationGroup_isClosed`, `chosenUpperRamificationGroup_isClosed`: they are closed, since `Gal(E/K)` is finite.

## Points to watch

- The valuation on `E` is a noncomputable choice; independence of the choice is not proved here (the file's comment places it in a companion module).
- The chosen structure has its value group in universe `0`; the lower groups are indexed by natural numbers, the upper groups by real numbers.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteGaloisLevel.lean`: the Lean file is the source byte for byte (SHA-256 `f8f77215de550bf0e73ddb27136c45586417cd4340a5325609f3662534dc56b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
