# Spanning invariant subspaces with disjoint constituents

This internal categorical helper constructs a coproduct from a family of actual
invariant subspaces whose supremum is the whole smooth complex representation
and whose distinct members share no irreducible actual subquotient. The index
universe and carrier universe are independent.

`invariantSubspaceCofan` consists of the literal inclusions into the original
representation. `invariantSubspaceCofanIsColimit` applies the published
constituent-disjointness criterion for independence, and identifies actual
summation with `DirectSum.coeLinearMap`. Independence gives injectivity;
the range formula and the spanning hypothesis give surjectivity. The published
`cofanIsColimitOfBijective` supplies the coproduct universal property.

`iSup_range_cofan_eq_top` proves that the images of the legs of any supplied
coproduct span its vertex. The quotient by their supremum annihilates every leg;
the universal property makes this quotient map zero, so every vector belongs
to that supremum.

These are derived algebraic constructions using Mathlib's direct sums and the
published actual smooth-representation subquotient helpers. They assert no
existence of a representation-theoretic block decomposition.
