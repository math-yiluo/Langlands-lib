# The different of an arbitrary subextension and upper orbit indices

Module `FontaineWintenberger.Ramification.Different.Subextension`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a tower of discrete valuation rings `A ⊆ B ⊆ C` with `C/A` Galois with group `G` and `B` the invariants of a subgroup `H` (not assumed normal), the file expresses the exponent of the different of `B/A` through the indices of `H ⊔ G^u`, where `G^u = upperRamificationGroup G u`. Throughout, `I₀` is the zeroth lower ramification group and `H₀ = H ⊓ I₀`.

## Results

Three lemmas `maximalIdeal_emultiplicity_*` give the order of a product, of a nonzero ideal, and of an extended ideal in a discrete valuation ring.

- `differentIdeal_order_tower`: `ord_C 𝔇(C/A) = ord_C 𝔇(C/B) + e(C/B) · ord_B 𝔇(B/A)` in `ℕ∞`; `differentIdeal_order_toNat_tower` is the version in `ℕ`.
- `herbrandFunction_nat_mul_card`: `φ(N) · |I₀| = Σ(i<N) |Gᵢ₊₁|`.
- `subgroup_upperRelIndex_deficit_integral`: `|H₀|` times the integral over `[0, φ(N)]` of `|I₀|/|H₀| − [I₀ : H₀ ⊔ G^u]` equals `Σ(i<N) (|Gᵢ₊₁| − |H ⊓ Gᵢ₊₁|)`; the action is assumed faithful.
- `upperOrbitIndex_eq_zeroIndex_mul_upperRelIndex`, `fixingIndex_eq_zeroIndex_mul_inertiaRatio`: `[G : H ⊔ G^u]` and `[G : H]` factor through `[G : H ⊔ I₀]`.
- `exists_prime_index_upperOrbitIndex_profile`: if `[G : H]` is prime and `H ⊔ I₀ = ⊤`, there is `b ≥ 0` with `[G : H ⊔ G^u] = 1` for `0 ≤ u ≤ b` and `= [G : H]` for `u > b`.
- `differentIdeal_order_eq_sum_lower_card_of_cutoff`: Hilbert's formula `ord_C 𝔇(C/A) = Σ(i<N) (|G_i| − 1)` for any `N` with `G_N = ⊥`.
- `subextension_different_order_mul_inertia_eq_lower_sum`, `subextension_different_order_eq_upperRelIndex_integral`, `subextension_different_order_eq_ramificationIdx_integral`, `subextension_different_order_eq_upperOrbitIndex_integral`: formulas for `ord_B 𝔇(B/A)`; the last reads `[G : H ⊔ I₀] · ord_B 𝔇(B/A) = [G:H] − [G : H ⊔ I₀] + ∫[0, φ(N)] ([G:H] − [G : H ⊔ G^u]) du`.
- `card_inertia_div_card_subgroup_inertia`: `|I₀|/|H₀| = e(B/A)`.
- `subextension_prime_degree_different_profile`: if `[G:H]` is prime and equals `e(B/A)`, there is one break `b ≥ 0` as above and `ord_B 𝔇(B/A) = ([G:H] − 1)(b + 1)`.

For `K` complete discretely valued with perfect residue field, `L/K` finite Galois and `M` an intermediate field: `intermediate_spectral_integer_isGaloisGroup`, `intermediate_spectral_zeroOrbitIndex_eq_residueDegree` (`[G : H ⊔ I₀]` is the residue degree of `M/K`), `intermediate_spectral_different_order_eq_upperOrbitIndex_integral`, and `intermediate_spectral_prime_degree_different_profile` specialize the above.

## Proofs

Hilbert's formulas for `C/A` and `C/B` are subtracted using transitivity of the different; sums over lower groups become integrals over upper groups by the Herbrand identity for subgroups, from an earlier file.

## What to watch for

- Formulas are finite-cutoff statements: they take `N` with `G_N = ⊥` and integrate up to `φ(N)`.
- Exponents appear as `(emultiplicity …).toNat` cast to `ℝ`.
- The general statements use `FractionRing` and assume `C` Henselian, finiteness, separability of `Frac C / Frac A`, and perfect residue fields of `A` and `B` (or a separable residue extension).

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Different/Subextension.lean` (SHA-256 of the source file `59a9807230b8a8f708a2aefffdc167bdd555c6fca49acb9818480192b118388a`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
