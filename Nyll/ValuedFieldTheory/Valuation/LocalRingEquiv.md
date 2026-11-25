# Maximal ideals under isomorphisms and extensions of local rings

Module `Nyll.ValuedFieldTheory.Valuation.LocalRingEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Short lemmas on how maximal ideals and their powers behave under maps of local rings, meant for transporting principal-unit filtrations between isomorphic valuation rings.

- `ringEquiv_map_maximalIdeal`, `ringEquiv_map_maximalIdeal_pow`: a ring isomorphism `e : R ≃+* S` of local rings maps the maximal ideal `𝔪_R` onto `𝔪_S`, and `𝔪_R ^ n` onto `𝔪_S ^ n`.
- `ringEquiv_mem_maximalIdeal_pow_iff`: `e x ∈ 𝔪_S ^ n` if and only if `x ∈ 𝔪_R ^ n`.
- `map_maximalIdeal_eq_pow_ramificationIdx`: for discrete valuation rings `R → S` with injective local algebra map, the extension of `𝔪_R` to `S` equals `𝔪_S ^ e`, where `e` is `Ideal.ramificationIdx'` of `𝔪_R` in `𝔪_S`. The proof writes the extended ideal as a power of the maximal ideal and identifies the exponent with the ramification index.

Any ring isomorphism between local rings is automatically local, so the first lemmas need no extra hypothesis on `e`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/LocalRingEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `5c1b32099d63b27a282778db880ace07ed85ef6cbd0edc983327aaf5949da208`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
