# Henniart's candidate existence over totally complex fields under the exact-stabilizer condition

The theorem `Langlands.Henniart.candidateExistenceExactStabilizerTCReduction`
has type

```lean
CandidateExistenceExactStabilizerTCReductionStatement.{uK, uW, uP, uE, uQ}
```

with all five universe levels independent. It takes the five hypotheses
of the published statement and constructs a candidate at each finite
quotient `q` of the absolute Galois group of a p-adic field `K`, with
automorphic lattice universe `0`.
[Target statement](HenniartCandidateExistenceExactStabilizerReductionStatement.md)

## Implemented proof

1. Local relative class formation supplies a family `I` at all primes
   with the relative class formation and arithmetic normalization
   properties. The existence part of `globalFundamentalClassStatement`
   gives the global fundamental class family `c` and its restriction
   properties. Together with `I` these witness
   `RelativeWeilGroup.IsArithmeticClassFamily c`.
   [Global fundamental classes](../ClassFieldTheory/Global/FundamentalClassProof.md)
2. `henniartGlobalizationExactStabilizerTC_of_inputs` is applied at `c`,
   `K` and `q` with the assumed Proposition 4.8 and Théorème 2.4.
   `harrisDatumCharacterRealizationExactStabilizer` produces the
   exact-stabilizer datum for the application of Harris's proposition.
   `LocalClassField.commonClosureReciprocityExistence` supplies the
   normalized local reciprocity family used by the datum. The other
   proved inputs are `RelativeWeilGroup.localInducedRestriction` for
   restriction of an induced relative Weil representation,
   `RelativeWeilGroup.associatedCentralCharacter` for the associated
   determinant and central character, and
   `RelativeWeilGroup.localTransferReciprocity` for the transfer used
   in unramified twisting. The globalization gives a totally complex
   field `F`, a Galois extension `E/F`, a place `v` with
   `h : residuePrime v = p` and `f : K ≃ₐ[ℚ_p] F_v`. It also gives
   a preimage in the relative Weil image for each unitary class
   supported on classes factoring through `q`, with equality in the
   exact Grothendieck group of `W_K`.
   [Globalization](../Global/Arithmetic/HenniartGlobalizationExactStabilizerTC.md),
   [Datum realization](../Global/Arithmetic/HenniartHarrisDatumExactStabilizerProof.md),
   [Reciprocity](../ClassFieldTheory/Local/CommonClosureExistenceProof.md),
   [Induced restriction](../VirtualRepresentation/Global/RelativeWeilLocalRestrictionProof.md),
   [Central character](../Automorphic/AssociatedCentralCharacterProof.md),
   [Local transfer](../ClassFieldTheory/Global/LocalRelativeWeilTransferProof.md)
3. `compactSpace_adeleQuotient` supplies compactness at `F`.
   Take `ψ` to be
   `HeckeFunctionalEquation.standardFiniteAdditiveComponent F v`.
   The totally complex witness at `F` lets the certified pole-comparison
   hypothesis give the comparisons at `v` for `ψ`.
   `relativePolePairing` turns these comparisons into the isometry `T`
   between the relative Weil and automorphic images, together with its
   `RelativeGeneratedPositiveIsometry` property.
   [Adele quotient compactness](../Global/AdeleQuotientCompactProof.md),
   [Additive character](../Automorphic/AssociatedAdditiveInputs.md),
   [Pole comparisons](../Global/Factors/PoleComparisonTCStatement.md),
   [Pole pairing](../Global/Factors/RelativePolePairingProof.md)
4. The candidate map is `henniartCompositeMap F E c v h K f T`, which
   transports `T` along the lattice identifications induced by `f`.
   The totally complex composite-map hypothesis gives its
   `HenniartProperties`. For each unitary class supported on classes
   factoring through `q`, the globalization supplies its preimage.
   `continuousRestrict_completionWeilTransport_eq_iff` converts the
   exact restriction equality into equality under
   `completionWeilLatticeEquiv`. This puts the class in the domain of
   the candidate.
   [Composite map and Weil transport](../Global/Factors/HenniartCompositeMapStatement.md)

This is the Library's relative version of Henniart (2000),
`henniart-2000-simple-proof`, Théorème 3.1 and §§3.3–3.8 (pp. 448–451),
with Théorème 2.4 (pp. 445–446) and the pole pairing from the comparison in
Lemme 2.8 (pp. 447–448). The auxiliary condition is Harris (1998),
`harris-1998-local-langlands`, (4.12) in the proof of Lemma 4.7 (p. 204),
used in the published exact-stabilizer form of Proposition 4.8 (p. 201).
[Registered originals](../../notes/henniart/sources.md)
