# Positive forms invariant under the actual relative Weyl quotient

Author: Worker 200.

This internal construction reuses the published relative Weyl action on the
full real character space of an actual split torus. A finite sum of pullbacks
of a positive coordinate form constructs a positive symmetric bilinear form
invariant under that action. No root set or analytic conclusion is an input.

The field and both actual group schemes live in an arbitrary universe, with
no restriction on characteristic. The morphism `i : T.toGrp → G` is an actual
monomorphism. `relativeWeylRealCharacterAction i` reuses
`relativeWeylFullRealAction i` from `Rational/RelativeCentralDirections`,
the scalar extension of the published `relativeWeylCharacterAction i` on the
entire character lattice. Its formula on `r ⊗ χ` is `r ⊗ w(χ)`, and on an
actual normalizer point it is the existing `characterRealAut`. The pairing
lemma reuses `Langlands.GroupScheme.pair_relativeWeyl`, preserving simultaneous
invariance of the existing character/cocharacter pairing.

The positive-form section additionally assumes `hT : IsSplitTorus T.toGrp`
and an enumeration `Fintype (relativeWeylGroup i)` of the actual quotient
`N(k)/Z(k)`. It does not infer this finiteness from arbitrary torus embeddings.
The existing finite-dimensionality theorem supplies a finite basis of
`RealTorusSpace.Vstar T`. `characterCoordinateForm` pulls the finite real dot
product back along its coordinate equivalence. It is noncanonical; no metric
independence of that choice is asserted. The diagonal is a sum of squares.
For a nonzero vector, coordinate injectivity supplies a nonzero coordinate,
and its square makes the sum strictly positive. Rank zero is included.

`relativeWeylInvariantForm i hT` is the unnormalized finite sum of that
coordinate form pulled back in both variables by every actual relative Weyl
class. Each summand is symmetric and nonnegative on the diagonal. The
identity summand proves strict positivity for every nonzero vector. Right
multiplication by a Weyl class permutes the finite sum, proving simultaneous
invariance. Strict positivity also proves left separation by testing a
putative radical vector against itself.

The provenance is internal finite-dimensional linear algebra from the
published actual lattices, real tensor spaces, integral quotient action and
finite-dimensionality theorem, together with Mathlib's dot product and finite
sum operations. No additional literature theorem is used or asserted.

For the Waldspurger Plancherel program this is a local pairing prerequisite.
It neither constructs the actual restricted roots in a parabolic radical nor
compares a pairing on a Levi split component with a single ambient pairing.
It constructs no convergence cone, normalized real-part comparison, open
orbit domain, rational continuation or intertwining operator. Those source
application obligations remain separate. In particular this module is not a
statement or proof of Waldspurger IV.1.1.
