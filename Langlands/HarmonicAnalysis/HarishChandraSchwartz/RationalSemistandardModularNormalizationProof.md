# The modular character of each actual semistandard parabolic

The theorem `Langlands.HarishChandraSchwartz.rationalSemistandardModularNormalization`
proves the proposition `RationalSemistandardModularNormalizationStatement` of
`RationalSemistandardFourierTransform`. Let `F` be a nonarchimedean local
field, `G` a connected reductive group over `F` and `i` a maximal split torus
of `G`. For every intrinsic semistandard index `p` of `i`, the modular
character of the rational points of the parabolic `parabolic p`, in the Haar
convention of `Measure.modularCharacter`, equals at each point `q` the Haar
modulus of conjugation by `q` on the closed normal subgroup `radical p`
(`HaarModulus.closedRestrictCharacter`). In Waldspurger's exposition this
is the modulus `δ_P` of a semistandard parabolic `P = MU`: I.1 introduces
the modulus `δ_H` of a closed subgroup `H` with its left Haar measures, and
I.3 normalizes parabolic induction by `δ_P^{1/2}`. The point topologies, the
field and the torus are those of the statement; nothing is added to its
hypotheses.

## Proof

The rational points of the parabolic are the semidirect product of the
Levi `levi p` and the radical `radical p` (`decomposition p`, an
`IsSemidirectDecomposition`). The theorem
`IsSemidirectDecomposition.modularCharacter_eq_restrictCharacter_of_unimodular`
computes the modular character of such a product as the conjugation modulus
on the normal factor, provided the projection onto the Levi factor is
continuous and both factors are unimodular. The proof supplies these three
inputs.

1. Continuity of the Levi projection is
   `RationalSemistandard.projectionContinuity`, applied to the given
   connected reductive group, maximal split torus and index.
2. The Levi is unimodular by `RationalSemistandard.levi_modularCharacter`,
   applied to the chosen reductive Levi model `chosenLeviModel p`; that
   theorem transports the unimodularity of the rational points of a
   connected reductive group through the model's point homeomorphism.
3. The radical is unimodular by `RationalSemistandard.radical_isUnimodular`,
   applied to the cocharacter presentation of `p` obtained by
   `CocharacterPresentation.ofCoverage` from the dynamic coverage theorem
   `semistandardSpectralDynamicCoverage`.

The local compactness instances needed to speak of Haar measures on the
three subgroups come from their closedness (`isClosed_levi_of_model`,
`isClosed_parabolic`, `isClosed_radical`). Rewriting with
`HaarModulus.closedRestrictCharacter_eq` identifies the resulting
conjugation modulus with the form used in `ModularNormalization`.

The theorem `RationalSemistandard.parabolic_modularCharacter` of
`RationalSemistandardWavePacket` proves the same identity from an
additional compact datum `CompactData p`. The proof here uses no such
datum: besides the decomposition and the two unimodularity theorems, its
only input is the continuity of the Levi projection, which
`projectionContinuity` proves for every index.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), no. 2, 235–333,
I.1 (printed p. 240) and I.3 (printed p. 243),
[doi:10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
