# Adic completeness of the valuation ring of a complete discretely valued field

Module `Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field with a valuation topology (`Valued K Γ`) whose valuation `v` is discrete of rank one (Mathlib's `Valuation.IsRankOneDiscrete`). The file shows that on the valuation ring `𝒪` of `v`, the subspace topology from `K` is the `𝔪`-adic topology for the maximal ideal `𝔪`, so that completeness of `K` gives adic completeness of `𝒪`.

## Main results

- `rankOneDiscreteValuationSubring_isDiscreteValuationRing`: `𝒪` is a discrete valuation ring.
- `rankOneDiscreteValuationSubring_isAdic`: the subspace topology on `𝒪` is the `𝔪`-adic topology (`IsAdic 𝔪`).
- `rankOneDiscreteValuationSubring_isAdicComplete`: if `K` is complete, `𝒪` is `𝔪`-adically complete.
- `completeDVFOfCompleteValuedField`: a complete such field, with its valuation, as a term of the library's structure `CompleteDVF K`.

## Proofs

With a uniformizer `π`, membership in `𝔪 ^ n` is the condition `v(x) ≤ v(π) ^ n`, an earlier result of the library. Each `𝔪 ^ n` is thus a closed ball of nonzero radius, hence open; conversely, a basic neighbourhood of 0 of radius `γ` contains some `𝔪 ^ n`, since `v(π) ^ n < γ` for large `n` (the value group is Archimedean, being isomorphic to `ℤₘ₀`). Completeness of `𝒪` comes from `𝒪` being closed in `K`.

## Points to watch

- `DVF` and `CompleteDVF` are the library's own structures (a field with a chosen value group and valuation), not Mathlib classes; the discrete valuation ring statement passes through `DVF`.
- The adic-topology result uses only the subspace topology on `𝒪`; completeness of `K` is needed only for the last two declarations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean`: the Lean file is the source byte for byte (SHA-256 `97f3f02951a4d3a336a636ce0432d9f5f578217708fcb520968fa0b848836a65`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
