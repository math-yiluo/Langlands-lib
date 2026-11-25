# Actual full-Levi orbit measure

This derived module compares the orbit measures in the ambient group-Levi packet
and the actual full-root standard Levi packet for Waldspurger VIII.4.2,
printed p.330 (PDF p.96), using the I.1 and VI.3 normalization.

The ambient connected reductive group, maximal split torus, generic
cocharacter, and supplied split component are retained. At all simple roots,
the literal Levi is identified with the ambient rational-point group.
`map_rationalFullLeviSplitCenter` proves that the factored split component has
exactly the supplied ambient point-image under this identification.

For the supplied arbitrary Borel ambient quotient Haar measure,
`rationalFullLeviQuotientHaar` is its pullback through the actual quotient
homeomorphism. It is proved to be Haar, and its pushforward equals the supplied
measure without a scalar. The normal subgroup and Borel structures of these
quotients are explicit interface inputs.

The discrete-series class is pulled back through the literal group
equivalence, on the same carrier universe. The actual character equivalence
and quotient measure equality provide the homeomorphism of twist orbits.
The finite self-twist hypotheses needed for their measure formulas are
discharged by the published split-component finiteness results.

`map_rationalFullLeviOrbitHomeomorph_measure` identifies the pushforward of
`rationalNormalizedDiscreteSeriesOrbitMeasure` with the literal packet's
`standardLeviNormalizedDiscreteSeriesOrbitMeasure`. It applies the exact
orbit transport and full-Levi character-measure comparison, retaining both
the source restriction-kernel cardinality and the self-twist cardinality.

The field and representation carrier universes remain independent. The module
proves no smooth-section comparison, packet membership, cuspidality or closed
VIII.4.2 target (`RationalCuspidalDiscreteCoefficientStatement`,
`RationalCuspidalFixedCoefficientLiftingStatement`).
