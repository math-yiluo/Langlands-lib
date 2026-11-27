# Continuous irreducible classes of a group quotient

`Langlands.FiniteRepresentation.continuousIrreducibleQuotientEquiv` identifies
the rank-\(n\) continuous irreducible complex representations of \(G/N\),
up to linear intertwining equivalence, with the corresponding classes of
\(G\) on which \(N\) acts trivially. It uses the quotient topology of the
normal subgroup \(N\) of \(G\). The group and carrier universes are
independent.

`IsomorphismClasses.IsTrivialOn` descends the subgroup containment in the
action kernel through the genuine isomorphism quotient. Intertwiners
identify the two kernels. `descendQuotient` constructs the action on the
original vector space by the quotient lift of the action homomorphism.
The identity on elements of \(G\) is `descendQuotient_mk`, and
`isContinuous_descendQuotient` uses the quotient topology to check
continuity after composition with the projection.

The forward class map is restriction along the quotient projection.
Surjectivity of the projection identifies invariant subspaces before and
after restriction and allows every intertwiner between the restrictions
to intertwine the actions of the quotient. This proves preservation of
irreducibility and injectivity on classes. To reach a class with trivial
action of \(N\), take a representative and descend its action. Inflation
of that descent acts on the same vector space with the original action,
so the identity is an intertwiner. All of these operations retain the
rank.

`forget_continuousIrreducibleQuotientEquiv` expresses the forward map on
ordinary isomorphism classes. The twist theorem uses that formula and
reduces to precomposition of the scalar twist on a representative. A
continuous character of the quotient has the same scalar action after
pullback as the original character evaluated on the quotient image.

This is the quotient-representation step used in the close-fields
comparison of Henniart, `henniart-1988-numerical`, SHA-256
`3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`,
§5.1, p. 512. The general comparison follows from factorization through
the group quotient and invariance of the intertwining relation.

[Group transport](../../VirtualRepresentation/Weil/GroupTransport.md) ·
[Twists on classes](TwistClasses.md)
