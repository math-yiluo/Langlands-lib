# The final quotient step for opposite Jacquet untwists

Worker 148. This internal assembly step uses an actual opposite standard
Jacquet exponent and its `UnitaryUntwist` record. The standard parabolic,
Levi, and split component are those of the original standard family.
The closed `LeviSecondAdjointnessStatement` is an explicit input.

`exists_surjective_standardInduction_untwist` composes the record's actual
retwisting isomorphism with its injective inclusion into the opposite
Jacquet module. The resulting map is injective and nonzero: the retwist is
irreducible and hence nonzero. The published actual opposite-parabolic
construction verifies both hypotheses of second adjointness, the equality
of ambient Levi maps and the intersection of rational-point images.
The supplied second adjointness and the cross-universe quotient bridge
then give a surjective intertwiner from actual standard induction of the
retwist onto the original irreducible ambient representation.

`standardInductionQuotientOfUntwist` selects such a map with its surjectivity
certificate. Classical choice makes no canonical selection assertion.
The field universe `u` and original carrier universe `v` remain independent.
The induced carrier lies in universe `max u v`, while the inducing
representation and ambient quotient keep their original carriers in `v`.

The provenance is internal composition of the actual opposite data,
untwisting record and induction/Jacquet carrier transport. This construction
does not prove second adjointness, temperedness, chamber membership, or the
Langlands classification.
