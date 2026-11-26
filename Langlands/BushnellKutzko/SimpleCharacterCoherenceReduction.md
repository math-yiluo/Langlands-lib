# Descending induction for coherence of simple character sets

`SimpleCharacterCoherenceReductionStatement` derives coherence from exact group carriers, adjacent restriction surjectivity and the intertwining test `SimpleCharacterCoherenceFibreStatement`. This is the descending argument in Bushnell and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (3.5.8), printed pp. 120–121 (PDF pp. 132–133). The source identifier is `bushnell-kutzko-1993-admissible-dual-gln` and the retained PDF SHA-256 is `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

At a depth below half the level, the intertwining test supplies a set of elements intertwining the quotient of any simple character from either set by a fixed common character. It also says that a character trivial on the next subgroup and intertwined by this set multiplies the common character into both sets. This is the test furnished by the source's core-approximation and determinant arguments.

The proof replaces each input stratum and defining sequence by its depth-zero presentation. It then descends on the nonnegative difference between half the level and the given depth. At or above half the level, the common member and the high-index value formulas give equality.

Below half the level the exact carrier formula identifies the next domain with the intersection of the given domain and the next unit filtration step. The common hereditary order determines that step. Thus the next domains agree, and adjacent restriction maps the common character into both next sets. The induction hypothesis identifies those sets, and restriction surjectivity identifies the images of the current sets.

For a current member `χ` of the first set, lift its restriction to a member `φ` of the second. The ratio `χ / φ` is trivial on the next domain. Every element of the supplied intertwining set intertwines it, since it is the ratio of `χ / θ` and `φ / θ` for the common member `θ`. The test puts `θ * (χ / φ)` in the second set. Ternary closure then puts `(θ * (χ / φ)) / θ * φ = χ` in that set. The same calculation exchanges the two sets.
