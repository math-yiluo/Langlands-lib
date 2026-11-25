# Multivariate rational functions

Module `StacksCore.FieldTheory.MvRatFunc.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines the field of rational functions in a family of variables over a ring, and gives extensionality principles for maps out of it.

- `MvRatFunc σ R`: an abbreviation for `FractionRing (MvPolynomial σ R)`, the rational functions in variables indexed by `σ` with coefficients in `R`.
- `MvRatFunc.ext_ringHom`: two ring homomorphisms from `MvRatFunc σ R` to a ring `A` are equal if they agree on the constants and on every variable `X i`.
- `MvRatFunc.ext_algHom`: two `R`-algebra homomorphisms from `MvRatFunc σ R` to an `R`-algebra `A` are equal if they agree on every variable. Both are registered as high-priority `ext` lemmas.

## Watch for

`MvRatFunc` is the library's own definition, not a Mathlib structure. It is defined for any commutative ring `R`; since Mathlib's `FractionRing` is the localization at non-zero-divisors, it is a field only when `R` is a domain.

## References

Tag 030E (part 2).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030E](https://stacks.math.columbia.edu/tag/030E) | `MvRatFunc` | 2 |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/FieldTheory/MvRatFunc/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 5 are kept. The 1 left out are not needed by the results for which the extract is made: `MvRatFunc.ofRatFunc`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
