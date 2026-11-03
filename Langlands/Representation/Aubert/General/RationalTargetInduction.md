# Actual target intersections in the rational standard Levi family

This internal adapter retains the point normalizer and full-centralizer
comparisons, the supplied Coxeter system, and both all-test twisted-intersection
properties used by `RationalTwistedIntersectionTransport`. It applies to every
minimum point Weyl representative and every normalizer lift of that
representative, over every field and the given affine ambient group scheme.
It does not require a finite or nonempty simple-root type.

`point_geometricTargetIntersections` identifies all three actual target
intersections with the literal standard Levi, parabolic and radical at
`intersectionSubset cs J I w⁻¹`, using the transported point Coxeter system.
The Levi equality is an ambient subgroup equality. The parabolic and radical
equalities are the literal subgroupOf restrictions inside `L_I`. The proof
applies the source identities with the two finite subsets exchanged and the
normalizer lift inverted. `isMinimal_inv` supplies minimum length, and
`QuotientGroup.mk_inv` supplies the inverse quotient-lift identity. Expanding
the intersection definitions gives exactly the target convention
`L_I ∩ n(-)n⁻¹`.

With the same connected reductivity, maximal split torus, generic cocharacter
and `StandardLeviIntersectionStatement` premises as the source adapter,
`pointTargetDecomposition` derives the actual target semidirect decomposition
from the source decomposition at those exchanged subsets and inverse lift.
No target decomposition is assumed.
`pointGeometricIntersectionDecompositions` packages the two derived
decompositions uniformly for every minimum representative and every lift.

`pointTargetLeviIdentity` reads the resulting target labels as the exact
`intersectionLeviIndex` inside `I`; `leviIndex_intersectionLeviIndex` ensures
that no finite label is lost. `pointTargetLeviInclusion` derives inclusion
in `L_I` from this actual intersection. Together with the source identity,
these equalities transport `geometricIntersectionMembership` to
`pointIntersectionConjugationMembership` for the two literal standard Levis.

Using the canonical evaluation topology `pointTopology` and
nonarchimedeanness of the rational-point group,
`pointIntersectionConjugationEquiv` is the resulting continuous inverse
conjugation equivalence from the target Levi to the source Levi. It sends
`x` to `n⁻¹ x n`, with the induced subgroup topologies. In particular the
direction agrees with the pullback used for forward representation transport.

Under local compactness of the rational-point group and closedness of the
actual standard Levis and radicals,
`pointTargetInductionFunctor` constructs the actual normalized target
induction functor, using the derived decomposition. Its representation
carriers have the independent-universe scope `max (u + 1) v`.
There is no finite-length or exactness assumption in this construction.

All provenance is internal through the named source adapters, Coxeter
inversion, quotient inversion and the existing actual intersection and
normalized functor definitions. The structural properties remain inputs.
Comparison with literal restricted induction, preservation, stages, Weyl
conjugacy, geometric expansion and the final rational-point Aubert induction
equation remain separate obligations; no premise is added to that target.
