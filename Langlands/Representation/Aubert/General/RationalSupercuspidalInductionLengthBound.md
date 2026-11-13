# Actual induction length from associated Jacquet detection

This is an internal conditional reduction of the length argument in Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026), VI.5.4,
printed pp.173–174 / PDF pp.179–180. It uses the actual standard rational
parabolics and Levis, not supplied replacement groups.

`hasCompositionLengthAtMost_of_equiv` transports bounded composition length
along an actual representation equivalence, including across independent
carrier universes. The equivalence gives an order isomorphism of the invariant
subspace lattices, through their group-algebra submodule lattices. Thus a
strict chain in the source maps to a strict chain in the target. The published
bounded-chain criterion produces an actual source composition series within
the same bound.

`pointSupercuspidalInduction_compositionLengthAtMost_sourceCosets` assumes
the rational associated nonzero Jacquet detection statement, together with
the explicit actual Coxeter, root-length, standard-Levi Weyl identification
and rational structural hypotheses. For an irreducible cuspidal source in an
arbitrary carrier universe, it bounds the length of its actual normalized
induction by the exact source-Levi coset image
`standardLeviTransporterSourceCosets i ν I`.

The proof lifts the inducing carrier to the universe of the detection
statement. Over the finite type of standard root subsets associated with the
source, Jacquet functors preserve short exact sequences. The exact equal-rank
Jacquet-length computation supplies their finite budgets. Every irreducible
subquotient of the induction belongs to its support category, so the detection
premise gives a nonzero Jacquet image at one of those indices. The finite-family
length theorem therefore gives an actual composition series with length at
most the sum of the Jacquet budgets. Injectivity of the target-subset labels
bounds this sum by all full-intersection pairs. The actual transporter
embedding bounds those pairs by the literal source-coset image. Finally, the
actual induction equivalence and the first helper descend the bounded
composition series to the original carrier universe.

`pointSupercuspidalInductionCompositionSeriesOfDetection` chooses the actual
composition series supplied by this bound. Its output retains the original
representation and its carrier universe, a length in the finite interval
bounded by the source-coset cardinality, and a proof that every grade is
irreducible.

The detection premise is retained. This module alone does not prove the
published unconditional Bernstein induction bounds statement.
