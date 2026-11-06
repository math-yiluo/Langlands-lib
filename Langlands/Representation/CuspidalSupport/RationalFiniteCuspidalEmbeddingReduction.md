# Rational finite embedding reduced to literal Levi Jacquet splittings

This is an internal reduction, authored by Worker 1570, of the existing
`RationalCuspidalInducedEmbeddingStatement`. It does not prove the required
splitting condition or the unconditional embedding theorem.

`RationalLeviJacquetCuspidalRemainderSplittingStatement` has exactly the
structural telescope of the published rational finite embedding target. For
each such family, each smooth object with carrier in `Type v`, and each
standard index, it asks for the actual Boolean cuspidal/remainder coproduct
of that object's normalized Jacquet module in the literal Levi. Cuspidality
uses the proper standard tests inside that same Levi. The field and group
universe `u` and source carrier universe `v` are independent.

`rationalCuspidalInducedEmbedding_of_leviJacquetSplittings` proves the
unchanged rational finite embedding proposition from this single additional
input. It supplies unimodularity and compact-limit regularity of the standard
unipotent radicals from the published rational regularity theorems. Nonzero
cuspidal Jacquet detection is supplied by Worker 1784's
`exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier`, whose proof
generalizes the earlier work of Workers 78 and 379. The supplied literal
splittings then give the detecting projections and finite orbit-map assembly
already constructed in `CuspidalJacquetProjectionFromSplitting`.

The conclusion retains the actual normalized inductions and finite direct
sum of the published target, with inducing carrier universe `max u v`.
The extra splitting input is explicit in this supporting theorem; it is not
added to or assumed by the original Library proposition. Establishing it
under the displayed structural hypotheses remains necessary for an
unconditional proof of that proposition.
