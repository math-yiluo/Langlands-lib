# π-adic digit expansions in a complete discretely valued field

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CompleteDVRExpansion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given a complete discretely valued field `K` (the library's `CompleteDVF`), a uniformizer `π` and a set of representatives of the residue field in the valuation ring `O`, the file constructs the digits of an element `u ∈ O`, with `u = a₀ + a₁π + ⋯ + aₙ₋₁πⁿ⁻¹ + πⁿ bₙ` at every stage, and the Laurent form `x = π^m u` of a nonzero element of `K`.

## Main definitions

- `residueRepresentativeSystemOf O`: for a local ring `O`, a section `repr` of the residue map with `repr 0 = 0`; `ofChoice` builds one by choice. `residueRepresentativeSystem F` is the case of the valuation ring of `F`.
- `remainder`, `coeff`: the recursive remainders `bₙ` and digits `aₙ = repr(residue bₙ)`, with `bₙ = aₙ + π bₙ₊₁` (`remainder_step`).
- `partialSum`: the partial sums of the terms `aᵢ πⁱ` over `i < n`.
- `PartialSumsConvergeAdically`: the partial sums tend to `u` for the `𝔪`-adic topology on `O`.
- `isLaurentExpansion F R π hπ x m u`: `u` is a unit, `x = π^m u`, the first digit of `u` is nonzero, the partial sums of `u` converge adically, and the finite-stage identities hold.

## Main results

- `partialSum_add_remainder`, `partialSum_congr`: `u` is the `n`-th partial sum plus `πⁿ bₙ`, so `u` minus the `n`-th partial sum lies in `𝔪ⁿ`; `partialSum_tendsto_adic`: the partial sums converge to `u`.
- `coeff_remainder_unique`: any sequences `bₙ`, `cₙ` with `b₀ = u`, `bₙ = cₙ + π bₙ₊₁` and every `cₙ` a chosen representative coincide with the remainders and digits above.
- `exists_laurent_unit`, `laurent_unit_unique`: every nonzero `x ∈ K` is `π^m u` with `m ∈ ℤ` and `u ∈ Oˣ`, and `m` and `u` are unique.
- `coeff_zero_ne_zero_of_isUnit`: the first digit of a unit is nonzero.
- `exists_unique_laurent_expansion`: for nonzero `x` there is a unique pair `(m, u)` satisfying `isLaurentExpansion`.

## Points to watch

- The uniqueness in `exists_unique_laurent_expansion` is that of the pair `(m, u)`; uniqueness of the digits is the separate statement `coeff_remainder_unique`.
- The file does not prove the converse direction of the classical theorem, that every sequence of representatives is the digit sequence of some element.
- Convergence is stated for the adic topology on a type-level copy of `O` (`WithTopology.toTopology`), not for a metric on `K`. The arguments use only the uniformizer and the representatives; completeness of `F` is not invoked.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/CompleteDVRExpansion.lean`: the Lean file is the source byte for byte (SHA-256 `f490ea0a95e72357cd5d44536e18c9595885f401c61f45ac030fdb331e134888`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
