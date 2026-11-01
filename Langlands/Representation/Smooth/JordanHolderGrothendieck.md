# Matching composition factors and the exact finite-length class

Author: Worker 320.

The helper `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_haveSameJordanHolderFactors`
identifies the exact Grothendieck classes of two actual finite-length smooth
representations whose composition factors match with multiplicities. It is
generic over a coefficient field, a topological group and an independent
carrier universe; both representations inhabit that carrier universe. The
finite-length witnesses in the conclusion can be any supplied proofs.

This is an internal consequence of the published irreducible realization
proof. The matching predicate supplies two actual simple-factor filtrations
and a permutation pairing equivariantly equivalent graded representations.
Isomorphism invariance of genuine irreducible labels identifies their sums
term by term; reindexing by that permutation identifies the whole sums. The
published `realize_seriesClass` theorem realizes each sum as its original
representation's exact class, and hence gives the claimed equality. Its
proof uses actual short exact relations, so this conclusion holds in the
full exact quotient, including nonsplit relations. No splitting, finite
vector-space dimension, admissibility or classification assumption is used.
This helper asserts only the indicated implication, not its converse.
