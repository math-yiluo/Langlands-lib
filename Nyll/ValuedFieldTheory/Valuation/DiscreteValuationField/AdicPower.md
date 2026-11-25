# Adic completeness for an ideal and for its powers

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Generic lemmas on adic completeness (Mathlib's `IsAdicComplete`, `IsHausdorff`, `IsPrecomplete`) of a module `M` over a commutative ring `R` with respect to an ideal. They show that completeness depends only on the topology defined by the ideal and is stable under the usual transports. Despite the namespace `ValuationTheory.DiscreteValuationField`, nothing here concerns valuations.

## Main results

- Powers: for `n > 0`, `M` is Hausdorff, precomplete or complete for `I` if and only if it is so for `Iⁿ` (`isHausdorff_pow_of_isHausdorff`, `isPrecomplete_pow_of_isPrecomplete`, `isAdicComplete_pow_of_isAdicComplete`, and the converses `isHausdorff_of_isHausdorff_pow`, `isPrecomplete_of_isPrecomplete_pow`, `isAdicComplete_of_isAdicComplete_pow`).
- `isAdicComplete_of_le_of_pow_le`: if `I ≤ J` and `Jⁿ ≤ I` with `n > 0`, completeness for `I` implies completeness for `J`. The form suits a finite integral extension, where the extended base ideal sits in the maximal ideal upstairs and a power of that maximal ideal lies in the extended ideal.
- `isAdicComplete_of_linearEquiv`: completeness for `I` is transported along an `R`-linear isomorphism `M ≃ N`.
- `isPrecomplete_map_algebraMap_iff`, `isAdicComplete_map_algebraMap_iff`: for an `R`-algebra `S`, `S` is precomplete (complete) for the extended ideal `I S` as an `S`-module if and only if it is so for `I` as an `R`-module; the helper lemmas compare `(I S)ⁿ` with `Iⁿ • S`.
- `isAdicComplete_map_ringEquiv`: completeness of `R` for `I` passes to `S` for the image of `I` under a ring isomorphism `R ≃ S`.

## Proof

The comparisons are by passing to subsequences `f (n·k)` of Cauchy sequences and comparing the filtrations `Iᵏ M` and `Jⁿᵏ M`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean`: the Lean file is the source byte for byte (SHA-256 `c7a715f976c948c2554e9f3054fed8b7ea81a4fb3a42fddcf9ed8c4781375c25`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
