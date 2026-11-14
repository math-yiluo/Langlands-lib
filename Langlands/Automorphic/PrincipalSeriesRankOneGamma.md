# Rank-one gamma factors of pairs of quasi-characters

Helper module for the principal-series pair gamma comparison.

## Definition (derived)

`tateRationalGamma F ψ ν χ` is Tate's local gamma factor of a quasi-character `χ` of
`F^×`, written as a rational function of `X = q^(-s)`:

`ε(0, χ, ψ, ν) X^(a(χ) + n(ψ)) · L(χ⁻¹)(q⁻¹ / X) / L(χ)(X)`,

where `L(χ)(X) = 1 / P_χ(X)` for Tate's Euler polynomial `P_χ`. Concretely it is `RankinSelberg.rationalGammaExpression δ c m P P'`, which is
`c X^m · P(X) / P'(δ / X)`, with:

- `δ = residueReflection F` (the scalar `q⁻¹`);
- `c = Padic.tateEpsilonCoefficient F ν χ ψ` (Tate's epsilon constant for the measure
  `ν`);
- `m = epsilonExponent χ ψ`, the sum of the conductor exponents of `χ` and `ψ`;
- `P = lPolynomial χ` and `P' = lPolynomial χ⁻¹`, Tate's Euler polynomials.

This is the usual `γ(s, χ, ψ) = ε(s, χ, ψ) L(1 - s, χ⁻¹) / L(s, χ)` (Tate's thesis;
JPSS 1983 for `GL_1 × GL_1`). It is derived by combining the Library's existing
rank-one epsilon and L data. It is used only as the common normal form of the two
sides of the comparison.

## Results

- `isGeneric_rankOneCharacter`: the character representation `χ ∘ det` of `GL_1` is
  generic for every nontrivial `ψ`.
- `isPadicPairGammaFactor_rankOneCharacters`: for a self-dual measure `ν`, the JPSS
  pair gamma factor of `χ ∘ det` and `η ∘ det` is `tateRationalGamma F ψ ν (χ * η)`.
  *Proof:* it combines the existing rank-one epsilon certificate
  (`isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss`) with the rank-one
  L-polynomial certificates for `(χ, η)` and for `(χ⁻¹, η⁻¹)` with `ψ` scaled by `-1`
  (`isPadicPairLPolynomial_of_rankOneCharacterEquiv`). The smooth duals are given by
  `Unramified.scalarCharacterSmoothDualEquiv`. The gamma factor then follows from
  `isPadicSymmetricGammaFactor_of_smoothDual` and the rank-`0` normalisation
  `isPadicSymmetricGammaFactor_of_le`. The identity `(χ η)⁻¹ = χ⁻¹ η⁻¹` matches the
  dual L-polynomial.
- `isPadicPairGammaFactor_of_rankOneCharacterEquiv`: the same formula for any
  representations equivalent to the two character representations, in independent
  carrier universes.
