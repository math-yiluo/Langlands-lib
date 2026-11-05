# Trivial positive-root stabilizers by integral averaging

This internal derived result proves `HasTrivialPositiveRootStabilizer i ν` for
every generic cocharacter of a maximal split torus in a connected reductive
group over an arbitrary field. It uses the actual quotient of rational
normalizing points by rational centralizing points.

The positive-root stabilizer is a subgroup of this finite quotient. Sum the
integral translates of the given cocharacter over that subgroup. Reindexing by
left multiplication shows that the sum is fixed by the subgroup. Pairing a
root with a translate equals pairing the inverse-translated root with the
original cocharacter. Stabilization of the positive roots and genericity
therefore make every summand have the same strict sign; their sum is nonzero.
Thus the sum is again generic, without dividing by the subgroup order.

The published normalizer/cocharacter centralizer criterion turns fixedness
into membership in the dynamic centralizer. The published generic-centralizer
theorem identifies that functor with the centralizer of the torus, so each
stabilizing Weyl class is trivial. No root datum, Borel subgroup, or reflection
generation hypothesis is used. The finite-averaging step is an internal proof
route, using the integral action and averaging pattern of
`WeylPositiveCocharacter`; it does not assert a new source theorem.
