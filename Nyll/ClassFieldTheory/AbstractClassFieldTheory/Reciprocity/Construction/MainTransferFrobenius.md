# Frobenius factors of the transfer and the matching norm decomposition

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Part of the proof, in the abstract class field theory of the library, that the reciprocity map is compatible with the transfer. The setting is a tower `K ⊆ K' ⊆ L` with `K'/K` finite of residue degree `f`, `L/K` and `L/K'` normal, `H` the image of `G(L̃/K')` in `G(L̃/K)` (Frobenius quotients modulo inertia), and a Frobenius element `σ` over `K` with fixed field `Σ`. Each orbit of `⟨σ⟩` on `G(L̃/K)/H`, with representative `t` and length `m`, gives a factor `t⁻¹σ^m t` of the transfer of `σ`. The file shows that this factor is a Frobenius element `β` over `K'` and describes its fixed field. It also proves the norm identity that the transfer side of the reciprocity square requires.

## Main results

- `transferNormNaturalityFrobeniusIntermediateEquiv`: `G(L̃/K') ≃ H`.
- `transferNormNaturality_zHat_positive_nat_of_nsmul_eq_nat`: in `ℤ̂`, if `f·z = N·1` with `f, N > 0`, then `z = n·1` for some `n > 0`.
- `transferNormNaturalityTransferFrobeniusLift`: the factor pulled back to `G(L̃/K')` as a Frobenius element `β`. Its degree is positive (`transferNormNaturalityFrobeniusTransferTermPreimage_degree`), and its closed cyclic subgroup maps onto that of `t⁻¹σ^m t`.
- `transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map`: the absolute group of the fixed field `Σ_t` of `β` is `G(K') ∩ t⁻¹G(Σ)t`, the stabilizer in `G(K')` of the coset of `t⁻¹` in `G(K)/G(Σ)`.
- `transferNormNaturalityTransferFrobenius_fixedField_le_conjugate` and `..._isUnramified_conjugate`: `Σ_t` is an unramified extension of the conjugate field `Σ^t`.
- `transferNormNaturalityTransferFrobenius_conjugatePrime_isPrime`: if `π` is a prime element of `Σ`, then `π^t`, viewed in `Σ_t`, is a prime element.
- `transferNormNaturalityNorm_eq_sum_transferNorms`: `N(Σ/K)(π)`, viewed in `A(K')`, equals the sum of the norms `N(Σ_t/K')(π^t)`. The sum runs over the orbits of `G(K')` on `G(K)/G(Σ)`, matched with the transfer orbits by `transferNormNaturalityTransferNormOrbitEquiv`.
- `transferNormNaturalityFrobeniusTransfer` and its `_doubleCoset_formula`: Mathlib's `MonoidHom.transfer` on `G(L̃/K)^ab → G(L̃/K')^ab`, written as a product of the factors above.

## Proofs

The degree of the factor satisfies `f·deg = m·n(σ)`, which the divisibility lemma in `ℤ̂` turns into a positive exponent. The fixed-subgroup description rests on `closedSubgroupGenerated_pow_eq_inf_stabilizer`. Unramifiedness holds because `Σ` and `Σ_t` both have the inertia of `L`. The norm identity splits `N(Σ/K)` along `G(K')`-orbits with chosen representatives (the inverses of the transfer representatives), and identifies each fiber with `G(K')/G(Σ_t)`.

## Watch for

- The conjugate field `Σ^t` is the subgroup `t⁻¹G(Σ)t`, and `π^t` is the action of `t⁻¹` on `π`.
- Orbit representatives are fixed choices (`Quotient.out`); several helper declarations are private.
- Most results assume `G` compact and Hausdorff; the unramifiedness and prime-element results also assume it totally disconnected.
- The prime-element result and the norm identity take fields of finite absolute degree (`FiniteAbstractFieldExtension G`) with `L/K'` finite (`hLfinite`); the norm identity holds for every `π` fixed by `Σ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `d8598e2d70d6331420843541b0334eb56b3975798226d11b00875bf708b61a2c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
