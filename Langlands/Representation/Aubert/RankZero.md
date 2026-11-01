# The actual Aubert operators in rank zero

Author: Worker 165.

This is an internal elementary construction supporting the all-rank
`Langlands.Aubert.InductionCommutationStatement`. Its intended exported result
`inductionCommutation_rankZero` proves the actual map equality when the ambient
rank is zero. The module does not prove positive-rank commutation.

The actual group `GL_0(F)` is a singleton. Positivity of every block size makes
the block-index set of a rank-zero shape empty, so its actual product Levi is
also a singleton. These facts imply that each representation action, including
the positive-half-modulus normalized inducing action and the inverse-half
normalized Jacquet action, is the identity at every group element.

The implemented constructions use actual carriers. Evaluation at the identity
is a linear equivalence from the actual smooth induced function space to its
inducing carrier; its inverse is the constant covariant function, whose uniform
open stabilizer is the whole group. The actual coinvariant quotient is linearly
equivalent to the original carrier: the identity linear map descends because
all group elements act trivially, and the actual quotient map is the inverse.
Composing these two equivalences gives
`inductionJacquetRankZeroEquiv` for the ordinary parabolic functors and
`refinedInductionJacquetRankZeroEquiv` for the actual product-Levi refinement
functors. Equivariance follows from the singleton ambient group.

These actual equivalences identify the corresponding exact Grothendieck
classes. The published generator formulas and extensionality on actual
finite-length objects then prove `inductionJacquetK0_rankZero` and
`refinedInductionJacquetK0_rankZero`, each an identity map on the relevant
exact Grothendieck group. The construction retains the defining relations
from every actual short exact sequence, including nonsplit sequences.

There is exactly one positive block shape of rank zero, namely the empty
shape, and exactly one refinement of its empty index set. The ambient
exponent `0 - C.length` is zero. The product-Levi exponent is also zero,
as follows either from the empty sum or the published
`refinementSignExponent_eq`. Thus both defining alternating sums have one
term of coefficient one. This proves `alternatingOperator_rankZero` and
`alternatingOperatorOnLevi_rankZero`; composing with the actual normalized
induction map gives `inductionCommutation_rankZero`.

All primes, supplied p-adic fields and topologies are retained. The field and
representation-carrier universes are independent. The representation
equivalences allow arbitrary carrier universe; the Grothendieck statements
use the prescribed saturated carrier `Type (max uF uV)`. There are no
admissibility, irreducibility, cuspidality, dimension, splitting or
additional preservation premises.

The provenance is the definitions of the actual functors and their exact
Grothendieck maps, with elementary singleton-group reasoning. This supplies
the rank-zero extension of the ambient/source conventions documented in the
unchanged commutation statement, rather than invoking the positive-rank
geometric lemma or a classification theorem.
