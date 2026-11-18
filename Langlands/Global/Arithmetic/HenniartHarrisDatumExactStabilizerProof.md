# Henniart's datum characters with exact Weil stabilizer

`Langlands.Global.harrisDatumCharacterRealizationExactStabilizer` proves
`HarrisDatumCharacterRealizationExactStabilizerStatement` at independent
universes `uF`, `uE`, `uE'`, and `uL`. It adapts the Library's
`HarrisDatumAuxiliary` and `HarrisDatumCharacterRealizationProof` to the
exact-stabilizer datum.

The auxiliary construction applies `auxiliaryCharacterFirstOrder` to the
copy of `F'` in its Galois closure. It takes `χs₀` to be the pullback along
the continuous isomorphism on units. Field norms from the closure to that
copy preserve the norm-one condition, since they are products of conjugates
and the spectral norm is invariant under the conjugations.
`hasExactUnitNormStabilizer_congr` therefore gives Henniart's unit-norm
stabilizer for any character agreeing with `χs₀` on units. For each
normalized reciprocity family, `unitNormWeilStabilizerTransport` gives the
exact stabilizer of the auxiliary Weil character restricted to the Weil
group of the closure.

The paired-place conditions make the selected places of `E'` disjoint from
their conjugates. `cmRegularUnitPrescription` supplies a conjugate-inverse
Hecke character `X` with distinct archimedean weights and the unit
prescriptions from `χ₀` and `χs₀`. For even degree `[E' : E]`, the proof uses
`cmHalfWeightCharacter` to choose a twist `ψ` that is unramified at both
places. For odd degree it takes `ψ = 1`. The weight identities give the
algebraicity twist at `[E' : E] − 1` and relative regularity of `ξ = X * ψ`.
The two local components transported along `φ` and `φs` give `χ` and `χs`.
The unramified twist preserves both unit prescriptions. Agreement with `χs₀`
supplies the exact Weil stabilizer, and `discreteValuation_eq_one_iff` gives
the required agreement of `χ` with `χ₀` on valuation-ring units.

The construction formalizes the unit prescription of Henniart 2000, §3.4
condition 3 and §3.6 Lemme 3, pp. 449 and 451
(`henniart-2000-simple-proof`). The auxiliary Weil condition is Harris 1998,
(4.12) in the proof of Lemma 4.7, p. 204
(`harris-1998-local-langlands`).
