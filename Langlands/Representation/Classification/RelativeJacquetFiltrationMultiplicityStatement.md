# Relative Jacquet multiplicities across a finite filtration

`Langlands.GLRelativeJacquetFiltrationMultiplicityStatement` is an internal
proposition definition, with independent universes `uF`, `uV`, and `uW`.
It contains two clauses for the existing actual functors
`RelativeJacquetMultiplicity.innerJacquet` and
`RelativeJacquetMultiplicity.ambientJacquet`. This file states their
finite-filtration multiplicity criteria; it contains no proof.

For every prime, p-adic field `F`, compatible topological data `T`, block
shape `B`, and refinement `S`, the input `A` is a bundled complex
representation of the coarse Levi `B.Levi F.Carrier`. It is assumed
smooth. The supplied `ObjectRepFiltration A l` is an actual finite
invariant filtration from zero to the whole representation, and its
`gradedRepresentation i` is the actual quotient at the original index
`i : Fin l`. The test representation `τ` is any bundled representation
of the common actual refined Levi `refinedLevi F.Carrier B S`.

The inner clause says that, for each natural number `m`,
`HasJordanHolderMultiplicity (innerJacquet T B S A) τ m` holds if and only
if there are natural counts at all original grades, each with
`HasJordanHolderMultiplicity` of
`innerJacquet T B S (s.gradedRepresentation i)` at `τ`, whose sum is `m`.
The ambient clause has the identical form with `ambientJacquet`.
Each multiplicity predicate includes existence of an actual finite
composition series with the specified factor count. Thus both
directions include finite-series witnesses; finite length is not an
additional hypothesis.

The ambient functor first applies the actual outer normalized induction
from the coarse Levi and then the actual composed opposite Jacquet
functor. Consequently its whole and grade carriers lie in
`max uF uV`; the inner carriers lie in `uV`. The independent universe
`uW` of `τ` is unchanged. All groups, right-translation induction
actions, positive upper half-modulus factors, and both factors of the
composed normalization are inherited from the existing constructions.

The rank and filtration length are arbitrary. Repeated steps and zero
grades retain their original indices. For length zero the sum is the
empty sum, and the same actual-series predicates apply. The statement
adds no irreducibility, admissibility, genericity, splitting, exactness,
or desired-comparison premise.

This is a derived internal adapter, not a transcription of a separate
literature theorem. Its intended proof specializes the normalized
opposite Jacquet filtration multiplicity theorem for the inner clause.
For the ambient clause, actual normalized induction filters the outer
induced representation, the composed opposite Jacquet multiplicity
theorem decomposes its count, and the normalized induction graded
equivalences transport each grade to the ambient functor of the
original coarse-Levi grade. That proof remains a separate obligation.

The statement supplies no inner-versus-ambient constituent inequality,
equality of Weyl totals, positivity or quotient criterion, or
irreducible-head conclusion. In particular it neither states nor proves
`GLRelativeGenericComparisonStatement`.
