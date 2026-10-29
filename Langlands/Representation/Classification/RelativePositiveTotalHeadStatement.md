# A strong head from equal positive relative Jacquet counts

`GLRelativePositiveTotalHeadStatement` is a closed proposition definition,
not a proof. It isolates the actual GL adapter needed after a positive
relative Jacquet multiplicity comparison.

For every prime, actual p-adic field `F`, compatible realization `T`, positive
rank `n`, block shape `B` and refinement `S`, let `μ` be an actual irreducible
admissible complex representation of the coarse Levi. Let `τ` be any actual
complex representation of the refined Levi. Assume:

* The actual outer normalized induction `I = I_B^G(μ)` has finite length as
  a module over the complex group algebra of `GL_n(F)`.
* For a natural number `m > 0`, the actual inner opposite Jacquet module
  `innerJacquet T B S μ` has `HasJordanHolderMultiplicity` equal to `m` at `τ`.
* The actual composed opposite Jacquet module `ambientJacquet T B S μ` of
  `I` has the same `HasJordanHolderMultiplicity` equal to `m` at `τ`.

The conclusion is the existing strong `Classification.HasIrreducibleHead`
of `I`: an irreducible quotient exists, and all actual irreducible quotient
maps have the same kernel, including maps to identical or isomorphic targets.
There is no supplied outer quotient or supplied quotient-image count bound.

The two multiplicity predicates each supply a genuine finite simple series
and its count. Finite length and the two equal positive counts remain
hypotheses. The statement does not supply these hypotheses for generic
inducing data. It requires neither irreducibility nor cuspidality of `τ`,
and imposes no parameter or genericity condition.

The field universe `uF`, test-carrier universe `uV` and inducing-carrier
universe `uW` are independent. The outer induced carrier has universe
`max uF uW`, and the existing head predicate tests quotient carriers in that
source universe. The refined subgroup and all normalizations are exactly
those of `RelativeJacquetMultiplicityStatement`: normalized upper outer
induction and normalized inner and composed opposite Jacquet modules.

## Internal derived provenance

This is an internal consequence of published Library interfaces, rather than
a new transcription of a literature theorem. The intended proof applies
`Classification.positiveTotalHeadCore` to the actual composed opposite
Jacquet functor. Given an irreducible quotient of `I`, admissibility descends
from normalized induction. Actual second adjointness turns its nonzero
quotient map into a nonzero map from `μ` into its opposite coarse Jacquet
module. Irreducibility of `μ` makes this map injective. Refined opposite
Jacquet exactness and transitivity then embed the actual inner Jacquet
module of `μ` into the actual composed opposite Jacquet module of that
quotient.

The functor sends the quotient map to a surjection. Short-exact
Jordan–Hölder decomposition of the supplied ambient series provides an
actual series count in its image. Injective multiplicity monotonicity makes
that count at least `m`. These are the quotient-image hypotheses of the
published positive-total head criterion. Nonvanishing follows from the
existing `CuspidalSupport.normalizedParabolicInduced_eval_surjective`, and
finite length gives an actual irreducible quotient via
`RegularHeadExistence.exists_irreducibleQuotient_of_finiteLength`.

This adapter leaves the unconditional GL finite-length and multiplicity
comparison theorems to their separate tasks. The generic comparison and
head family is not established by this proposition definition.
