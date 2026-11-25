# Restriction of automorphisms between intermediate fields

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For intermediate fields `E ≤ F` of one extension `Ω / K`, with `E / K` normal, the file gives the restriction map `Aut_K(F) → Aut_K(E)` without the caller having to install `F` as an algebra over `E`.

## Main declarations

- `intermediateFieldRestrictNormalHom E F hEF`: the group homomorphism `(F ≃ₐ[K] F) →* (E ≃ₐ[K] E)`, built from Mathlib's `AlgEquiv.restrictNormalHom` after making `F` an `E`-algebra through the inclusion `E ≤ F`.
- `intermediateFieldRestrictNormalHom_apply_val`: for `σ ∈ Aut_K(F)` and `x ∈ E`, the restriction of `σ` sends `x` to `σ(x)`, both read in `Ω`.
- `intermediateFieldRestrictNormalHom_equiv_commutes`: if `e : L ≃ₐ[K] F` identifies a field `L` with `F` and `σ ∈ Gal(L/K)`, then `σ` acts on the image of `E` in `L` through the restriction of the transported automorphism `e σ e⁻¹`.

## Watch for

Only normality of `E / K` is assumed; `F / K` need not be normal, finite or Galois.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `36d04c0bb0678379cdf621359e073e9ca0c152a09dc5e26985c3ffe3a04d3136`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
