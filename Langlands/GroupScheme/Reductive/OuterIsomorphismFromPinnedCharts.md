# Outer-isomorphism quotients from pinned constant charts

This internal reduction composes the supplied Isom and relative adjoint
quotient interfaces, actual affine pinned atlases, constant-parameter
geometry and effective quotient descent. It takes an explicit proof of
`PinnedOuterIsomorphismChartStatement` as an input.

First, the pinned chart statement applies to any two actual groups
identified with the supplied models. Source precomposition and target
postcomposition retain the parameter of the original Isom representative.
Precomposing the quotient map by the inverse source comparison retains
the same adjoint target and transports its canonical inner action.
The proved action identities therefore give the chart's constant family
directly in the original supplied representative, with its original
canonical action.

For a reductive group over an arbitrary scheme, the tests on which its
actual pullback is a supplied affine pinned model form a sieve.
The pullback comparison for iterated base change proves stability under
refinement. Its proved affine pinned étale atlas lies in the sieve, so
the sieve is an fppf covering sieve. Intersecting the two covering sieves
gives tests on which both groups have the required supplied pinned models.

On every such test, the chart input provides a constant family with a
unique adjoint decomposition on every scheme over that test. The local
section bridge reinterprets this as the full parameter-preserving family
over the original base. The constant parameter is separated, locally
quasi-finite and locally of finite type over the local base, including
when its type of labels is empty or infinite.

The adjoint target is smooth and affine over the base, hence flat,
locally of finite presentation and quasi-compact there. Its canonical
inner action is faithful because the quotient kills exactly the full
scheme-theoretic centre. `quotientRepresentationOfPinnedOuterCharts`
passes the resulting free action and the local sections to
`SchemeAction.quotientRepresentationOfLocalSections`. This retains the
representation of the canonical action quotient and its class map for
use by the geometry theorems. `outerOfPinnedOuterCharts` applies
`GroupIsomorphismScheme.outerOfQuotientRepresentation` to the same data.
Its class map is flat, surjective and quasi-compact, and the unique
adjoint difference is on each original relative test.

The reduction works over every base scheme. The final theorem specializes
the constructor to prove the generic DVR existence statement from the
same explicit pinned chart input.
