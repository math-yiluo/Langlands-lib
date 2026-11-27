# Nonsplit fundamental strata over the integers of an extension field

Source context: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, Definition (2.3.3) and (2.3.4), printed p. 58 (PDF p. 70). In the final step of the proof of (2.4.1)(i), printed p. 70 (PDF p. 82), (2.3.4) is applied over the field `E = F[γ]` to the derived stratum, which the Library represents over `subfieldIntegers F E`. The Library proposition `NonsplitRefinementPremise` states (2.3.4) for strata over the integer ring `𝒪[F]` of a local field. This module transfers a derived stratum to `𝒪[E]` for the spectral local-field structure on `E`, checks the hypothesis `Stratum.IsNonsplit` there, and transfers the conclusion back.

## Reduction of polynomials

- `coeff_reduceIntegralPolynomial`: for injective `O → K`, the coefficients of `reduceIntegralPolynomial O K p` are the reductions of the lifted coefficients, and zero where no lift exists.
- `reduceIntegralPolynomial_monic`: the reduction of a monic polynomial is monic of the same degree, if the residue ring is nontrivial.
- `map_jacobson_ringEquiv` and `reduceIntegralPolynomial_ringEquiv`: a ring isomorphism `φ : O ≃ O'` compatible with the maps to `K` maps Jacobson radicals to Jacobson radicals. Reduction over `O'` is the image of reduction over `O` under the induced isomorphism of residue rings (`Ideal.quotientEquiv`).
- `exists_eq_pow_of_not_two_factors`: over a field, a monic polynomial of positive degree with no two distinct monic irreducible factors is a positive power of a monic irreducible polynomial. All its normalized factors are then equal.

## Transfer of strata

`transferStratum S φ hφ` is the stratum with the chain `S.chain.transfer φ hφ` and the same integers and element. It has the same lattices and coset (`coe_transferStratum_lattice`, `coset_transferStratum`). It is fundamental exactly when `S` is (`isFundamental_transferStratum_iff`), and simple when `S` is (`isSimple_transferStratum`). Over discrete valuation rings it has the same period (`period_transferStratum`). Its polynomial `φ_b` for the transferred prime element `transferPrime φ π` is the image of that of `S` (`fundamentalPolynomial_transferStratum`).

## (2.3.4) over `𝔬_E`

`exists_simple_of_not_isSplit` assumes `NonsplitRefinementPremise` for fields in the universe of `E`. Let `D` be a fundamental stratum over `subfieldIntegers F E` that is not split. Then there is a simple stratum `C` over `subfieldIntegers F E` with `C.r = C.n − 1`, `D.coset ⊆ C.coset` and `D.n · e(C) = C.n · e(D)`, every lattice of `D.chain` being a lattice of `C.chain`.

Proof: for a prime element `π` of the discrete valuation ring `subfieldIntegers F E`, `φ_b(π)` is monic of degree `dim_E V ≥ 1` over the residue field. Since `D` is not split, it is a power of one monic irreducible polynomial (`exists_eq_pow_of_not_two_factors`). Transferring along `subfieldIntegerEquiv F E` makes the transferred stratum nonsplit in the sense of `Stratum.IsNonsplit`, for the transferred prime element. Apply `NonsplitRefinementPremise` over `E` and transfer the resulting simple stratum back along the inverse isomorphism.
